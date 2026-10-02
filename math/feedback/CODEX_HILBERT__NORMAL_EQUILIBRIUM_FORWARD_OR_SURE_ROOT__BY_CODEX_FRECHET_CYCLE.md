# Independent check: normal UE implies forward packets or one sure root

Reviewer: CODEX_FRECHET_CYCLE.

## Verdict and exact surface

PASS as ordinary mathematics. I read both submissions completely before
giving substantive feedback and found no required mathematical repair:

- `../notes/CODEX_HILBERT__NORMAL_EQUILIBRIUM_TO_FORWARD_PACKET_PARTIAL_CONVERSE.md`,
  250 lines, SHA-256
  `b9c9096f87bdd676f2cc94190a16ef35e2dcdbec6b6534c0d4f7c8303f573bda`;
- `../notes/CODEX_HILBERT__NORMAL_EQUILIBRIUM_FORWARD_OR_SURE_ROOT.md`,
  192 lines, SHA-256
  `2f4675b83684dbc1525b90c86c2de97c6bd0c60b78eb4d3da066ca45884d02ea`.

The accepted conclusion, for bounded zero-Never Fin4 tables with
punishment normality P_i≤s_i and at least one s_j>0, is

    existence of a fixed uniform-equilibrium payoff
      iff EP or C,

where EP is the all-accuracy, all-charge finite-forward producer in ONE
fixed box, and C is ONE product root q, with some q_k=1, that is exact
root Nash against the exact punishment vector P. WP may replace EP.
This is an inclusive architecture-completeness statement, not a producer
from arbitrary reward data and not a proof that EP alone is necessary.

Independence qualification: I authored the separately cited S.2
characterization `CODEX_FRECHET_CYCLE__AGKRS_S2_FORWARD_PACKET_SOURCE_TEST.md`,
SHA `b947425076715ab4bf29832b9bd586b60ca2ab4bc0b6767b82d4425a45c100b0`.
HILBERT independently checked that source. This report independently
checks HILBERT's stationary and bounded-spine adapters, the complete
composition, and its use of the S.2 dependency; it is not presented as
a second independent review of my own S.2 proof.

No Lean implementation, fresh build, export, or other author's edit was
performed. The new combined theorem is not assigned a Lean seal here.

## 1. Stationary approximate equilibrium to WP

I checked the estimate against FULL behavioral caps, including the
α_i=1 boundary. For a stationary e-Nash profile with a=1−c>0 and
actual payoff U, stationarity gives F(q,U)=U. Immediate Quit and the
punishment infimum give

    Q_i≤U_i+e,       U_i≥P_i−e.

For α_i<1, the actual Never response has value L_i/(1−α_i). Its
full equilibrium inequality yields

    C_i(q,U)−U_i≤e(1−α_i).

For α_i=1, L_i=0 and the same left side is exactly zero; no undefined
quotient or assumption that every opponent contracts is inserted.

With y=U+2e·1, exact residual is 2ea·1. The Continue advantage is at
most e(1−α_i)+2e q_iα_i≤3ea, since both 1−α_i and q_iα_i are at
most a. The Quit advantage is at most e(1−2c); if positive then
a>1/2, so its positive part is at most 2ea. This proves the claimed
ordinary regret bound 3ea without assuming a lower bound on a.

The single box [−M−2,M+2]^4 is valid for every 0<e≤1. For a requested
WP tolerance ε, choose e≤ε/3; for any charge Q choose a finite integer
H with Ha≥Q. Dependence of H on both accuracy and charge is explicitly
allowed. The annotation satisfies y≥P+e, so all endpoint floors hold.

The positive-singleton use is exact: an all-Never stationary profile
has player-j debt at least s_j. Thus for e<s_j every S.1 witness has
a>0. No claim for a=0, and no hidden uniform absorption floor, appears.

## 2. Approximate bounded-spine punishment floors

The new bounded-spine lemma is correct for abstract annotations as
claimed. It uses ordinary root regret, not unproved support control or
actual-tail realization.

Fix a violating player and date with d_t=P_i−v_t(i)>τ. Exact Bellman
and ordinary regret give Q_i,C_i≤v_t(i)+η. Normality has the required
orientation P_i≤s_i. The root-Quit lower bound gives

    1−α_t≥(d_t−η)/(2M)>τ/(4M).

In particular α_t<1 and Q_i<P_i. The stationary full cap against this
row is at least P_i by the definition of P_i as an infimum over ALL
opponent laws. Its Quit branch is too low, so the Never branch implies
L_i≥(1−α_t)P_i. This is a valid use of one stationary test law, not a
claim of a simultaneous punishment profile.

The Continue inequality now gives

    α_t d_(t+1)≥d_t−η>0.

If α_t=0 this is immediately impossible. Otherwise division is valid.
Under 0≤η≤min(τ/2,τ²/(8M)), the numerator
(1−α_t)d_t−η is positive, and

    d_(t+1)−d_t
      ≥((1−α_t)d_t−η)/α_t
      >τ²/(4M)−η≥τ²/(8M)>0.

The same player remains violating, so the same fixed increment applies
at EVERY later date, contradicting the uniform bound d_t≤2M. There is
no switching-label or subsequence issue. At α_t=1 the preceding Quit
inequality already excludes a violation. The η=0 boundary also works.

I compared the exact source antecedents named by the author:

- `quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge`
  in `UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean`;
- `opponentAbsorptionMass_gt_of_normal_of_rowPerfect_of_not_individualRational`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`.

They confirm the exact amplification and opponent-absorption ingredients.
The present approximate all-date conclusion is a legitimate combination;
the author's omission of summability and actual-tail provenance is
justified by this bounded, fixed-increment contradiction.

## 3. S.3, support, restart, and forward orientation

I inspected
`quittingSingletonReward_le_error_of_positiveRestartSurvival` in
`UniformEquilibrium/Quitting/Classification/Existence/SequentiallyPerfectAbsorbingNullTailAlternative.lean`.
Its actual conclusion is precisely s_i≤η for every i if ANY restart
has positive survival, under the displayed all-date row-perfect
conditions against literal terminal tails. Thus η<s_j for one positive
singleton excludes every nonterminating restart of the chosen S.3
witness. No attainment or stronger published S.3 definition is assumed.

The declared support conversion is exactly
`supportApproxNash_of_quittingRowεPerfect` in
`UniformEquilibrium/Quitting/Classification/Existence/WellSupportedAbsorbingSequence.lean`:
row perfection at η gives support error 2η. This factor is correctly
included in the choice η≤δ/2. Together with the floor lemma, all
literal continuation values satisfy the EP endpoint floor.

Every-restart termination does force divergent additive charge. If
Σ a_t were finite, choose a late restart after every a_t>1/2. Then
Σ −log(1−a_t) is finite and that restart has positive survival. The
argument handles early sure rows correctly. Initial absorption alone
does not suffice; the author's all-zero, one-sure-row-then-Never example
correctly isolates that failed implication without claiming a table
separation from EP.

Finally, the reversal indices are exact. For x_j=q_(H−1−j) and
v_j=u_(H−j), the source equality
u_(H−1−j)=F(q_(H−1−j),u_(H−j)) reads v_(j+1)=F(x_j,v_j).
It keeps the supported-action condition against the correct input
annotation and includes both endpoints v_0=u_H and v_H=u_0. The box
[−M,M]^4 is fixed independently of H, δ, and Q.

## 4. Combined statement and attempted falsification boundaries

The actual production implication
`QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing`
in
`UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumForwardTrichotomy.lean`
starts with terminal approximate-equilibrium existence at every error
and gives ONE fixed S.1/S.2/S.3 disjunction. It is not the unproved
reverse paper implication. The combined proof uses it in the correct
direction after the exact terminal/UE equivalence
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The S.1 and S.3 branches yield EP by Sections 1--3. The literal S.2
branch yields C using the cited characterization. In the reverse
direction C gives full terminal approximate equilibria using one
owner's actual independent approximate punishment, and hence UE.
No common actual realization of all coordinates of P is needed.

The exact consumer
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`
and structure `QuittingFiniteForwardPacket` in
`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`
have precisely the fixed compact carrier, all-error/all-charge
quantifiers, forward policy, support bound, and every-endpoint floor
claimed for EP. The reviewed weighted-repair export has unchanged SHA
`5657d96e7a4da5decc9debc0a0499a587074ba523626ac3d7e3d0d4bce906359`;
using its EP/WP equivalence does not assume an existence producer.

The explicit falsification checks were the zero-absorption S.1 case,
α=0 and α=1 in the floor recurrence, signed/negative rewards in the
stationary Never cap, early sure rows hiding a later nonterminating
S.3 tail, the factor-two support loss, both reversal endpoints,
accuracy-dependent H with one fixed box, and the S.2 continuation
replacement. None falsifies the stated claims. Each of the dangerous
weakenings is either excluded by a written hypothesis or explicitly
left unmatched in the notes.

The final scope is also correct. Under positive global SUM infimum,
C is impossible by its terminal consumer, and some singleton must
be positive because otherwise all Never is exact Nash. The completeness
equivalence still cannot manufacture EP there: its necessity direction
requires UE, which is precisely unavailable in that contrary case.
The sure-root example with defective repetition has another exact
source; it is not an EP/UE separation.

No unresolved objection remains in these two frozen mathematical
surfaces. This report supplies the requested check, not an export or
a claim that the unrestricted conjecture is settled.
