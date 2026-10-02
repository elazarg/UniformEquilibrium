# Weighted participant premiums supply the classical low-payoff root consumer

Author: CODEX_FRECHET_CYCLE. The weighted-coalition direction was proposed
by ROOT.

Status: complete ordinary-mathematical candidate, frozen for independent
review. The finite identity, actual-table attachment, and exact separation
examples are proved below. No export, Lean implementation, algorithmic
complexity bound, or worldwide priority claim. The classical charged-row,
periodic-tail, and full-response consumer is credited explicitly.

## 1. Exact finite reward condition and conclusion

Let I be a finite nonempty player set. The reward at every nonempty quitting
coalition S⊆I is r(S)∈ℝ^I, and Never pays zero. All players use independent
private behavioral randomization. A unilateral deviator may replace its
entire behavioral law, including by Never or any finite quitting time.
Put s_i=r_i({i}), and assume s_i≥0 for every player.

Suppose there is ONE vector λ with λ_i>0 for EVERY i such that

    Σ_(i∈S) λ_i [r_i(S)−s_i]≤0
                                     for every nonempty S⊆I.    (MP)

The sum is over MEMBERS of the quitting coalition only. Passive rewards
r_i(S), i∉S, are completely unrestricted signed real numbers. The weights
are fixed before the root, continuation, or accuracy is chosen; they do not
vary separately with S. Own premiums may have either sign.

THEOREM. Every table satisfying these hypotheses has actual terminal
approximate Nash profiles at every positive error against every unilateral
behavioral deviation. They may be chosen periodic from date zero with the
same full terminal error bound in every suffix. Consequently the original
table has one fixed uniform-equilibrium payoff.

The target is fixed before accuracy. Periods, strategies, and the finite
horizon thresholds may depend on accuracy. No stationary equilibrium or
prescribed finite stopping menu is assumed. A uniform-equilibrium payoff
means that every sufficiently long finite-horizon expected average payoff
is near the target and every unilateral behavioral deviation gains at most
the requested error. Active-stage rewards are zero and absorption repeats
the terminal reward thereafter.

The data condition is finite: one strictly positive vector satisfies one
linear inequality per nonempty coalition. It is not a supplied equilibrium,
root selector, social-payoff guarantee, or actual-tail certificate.

## 2. Exact product identity: the membership factors are essential

For q∈[0,1]^I let

    p_q(S)=∏_(i∈S)q_i ∏_(i∉S)(1−q_i),
    a(q)=1−∏_i(1−q_i),
    Q_i(q)=Σ_(T⊆I\{i}) p_(q,−i)(T) r_i(T∪{i}).

Here q_i is the probability of Quit and Q_i is the pure-Quit endpoint
against the independent opponent root. Write d_i(S)=r_i(S)−s_i for i∈S.
For each i,

    q_i[Q_i(q)−s_i]
      =Σ_(S∋i) p_q(S)d_i(S),

because q_i p_(q,−i)(S\{i})=p_q(S). This identity remains valid at q_i=0
and q_i=1; no division by a hazard is used. Finite summation gives

    Σ_i λ_i q_i[Q_i(q)−s_i]
      =Σ_(S≠∅)p_q(S) Σ_(i∈S)λ_i d_i(S).                      (1)

Thus (MP) implies

    Σ_i λ_i q_i[Q_i(q)−s_i]≤0                 for EVERY q.       (2)

Conversely (2) for every product root implies (MP), by choosing the pure
root whose quitting set is exactly S. Therefore (MP) is equivalent to this
global weighted endpoint inequality for the same λ.

If a(q)>0, its active set A={i:q_i>0} is nonempty. Since λ_i q_i>0
for every i∈A, (2) implies

    Q_i(q)≤s_i                               for some i∈A.       (3)

This holds for EVERY absorbing product root, without any Nash premise or
continuation restriction. At an exact Nash root against any continuation v,
Quit being supported further gives F_i(q,v)=Q_i(q)≤s_i.

The identity is NOT Σ_i λ_i(Q_i−s_i)≤0. For example, with two players,
pair premiums (1,−1), singleton premiums zero, λ=(1,1), and
q=(1/4,3/4), the endpoint premiums are (3/4,−1/4). Their plain sum is
1/2>0, whereas the correctly membership-weighted sum is zero.

## 3. Unit singleton levels feed the old consumer

First suppose s_i=1 for all i. Let R≥1 bound all absolute rewards and let

    W={v∈[−R,R]^I : some v_i≤1}.

For a product root define F(q,v)=Σ_(S≠∅)p_q(S)r(S)+(1−a(q))v, and
let C_i(q,v) be the pure Continue endpoint. Exact root Nash means
F_i=max(Q_i,C_i) for every player. Finite-game Nash existence supplies at
least one exact root at every v.

At v∈W, every absorbing exact root has an active i with F_i=Q_i≤1 by
(3). If the exact root is all-Continue, exact Nash instead gives v_j≥1
for all j, so membership in W supplies i with v_i=1 and both actions
indifferent. This is precisely the active-low-payoff root condition of
Solan--Vieille Proposition 2.2. It does not require weak support peeling.

For completeness the finite producer and its full consumer are spelled out
here rather than replacing them by a supplied sequence field.

Choose 0<δ≤1 and raise the selected player's Quit probability to
q'_i=q_i+δ(1−q_i). If it was active and mixed, its endpoints are equal;
if it was surely Quit, the root is unchanged; if all players Continued, the
newly introduced Quit action is indifferent. Thus its payoff stays at most
1, and a(q')≥δ. The Bellman successor remains in W. Every other player's
support is unchanged and each of its two pure payoffs changes by at most
2Rδ. Hence every supported action is within 4Rδ of the best pure action.
This is support regret, not merely ordinary mixed regret.

For a desired row tolerance τ>0 take

    δ=min(1/2,τ/(8R)),           ζ=δτ/4.

Choose a finite ζ-net in compact W. At every representative choose the
preceding root and map its successor to a nearby representative. A self-map
of a finite nonempty set has a cycle. Reverse its construction order to get
periodic roots q_ℓ and annotations v_ℓ satisfying

    |v_ℓ−F(q_ℓ,v_(ℓ+1))|∞≤ζ,
    a(q_ℓ)≥δ,
    support regret against v_(ℓ+1)≤4Rδ.

Repeat the product rows chronologically. Every suffix terminates since
survival for n further rows is at most (1−δ)^n. Its actual periodic
terminal suffix values U_ℓ obey U_ℓ=F(q_ℓ,U_(ℓ+1)). Taking the maximum
error over one period gives

    max_ℓ |U_ℓ−v_ℓ|∞≤ζ/δ.

Each pure endpoint is 1-Lipschitz in its continuation coordinate. Therefore
the rows have support regret at most 4Rδ+2ζ/δ≤τ against their ACTUAL
next-tail values. The construction uses independent product rows, not a
correlated mixture of profiles, and needs no continuous root selection.

The existing nonlocal consumer is
`quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
in `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
It requires unit singletons, not capped joint rewards: for every full
terminal error η>0 it supplies a positive row tolerance τ which makes
such a periodic, positively absorbing actual-tail-perfect sequence yield
a periodic profile whose every suffix is terminal η-Nash against ALL
behavioral deviations. The output can be a stationary repair rather than
the generated profile itself. The support inequalities above imply the
production `QuittingRowεPerfect` predicate by taking convex combinations
of supported endpoints.

Choose that τ before the finite construction. This completes the unit case.
There is no invalid summation of per-row errors in place of the full-response
extraction.

## 4. Exact weight transport and the nonnegative singleton boundary

For general s_i≥0 and t>0 define

    h_i=s_i+t>0,
    hat r_i(S)=[r_i(S)+t]/h_i,
    hat λ_i=λ_i h_i.

The transformed own singleton is 1 and the transformed participant premium
is d_i(S)/h_i. Therefore

    Σ_(i∈S)hat λ_i[hat r_i(S)−1]
      =Σ_(i∈S)λ_i[r_i(S)−s_i]≤0.                             (4)

All transformed weights are strictly positive. Keeping λ unchanged after
playerwise normalization would not generally preserve the constraint; the
factor h_i in hat λ_i is essential. Neither the transformed reward bound
nor the transformed weights must be uniform as t→0.

Never is zero in the original, shifted, and normalized games. Given desired
original full terminal error ε>0, set t=ε/4 and η=ε/2. Apply the unit
case to hat r, hat λ with full error η/max_i h_i. Undoing the positive
coordinate scales gives error at most η for r+t. For every profile π,
including every unilateral deviation and every suffix,

    U_i(r+t,π)−U_i(r,π)=t·P_π(absorption)∈[0,t].                (5)

Thus the original error is at most η+2t=ε. No absorption-one hypothesis
on deviators is needed. Periodicity and the every-suffix error bound survive.

Finally use
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
It selects one fixed original-table target before accuracy for every finite
player set. This is the unrestricted behavioral UE conclusion. No punishment
value, floor, or equality P=s is assumed or inferred.

## 5. Exact class separation from ordered positive premiums

### 5.1 Weighted cancellation with failed peeling

Take I=ℤ/4ℤ, s=(1,0,0,0), and orient the four adjacent pairs
S_j={j,j+1}, with indices modulo 4. On each adjacent pair give its first
member premium +1 and its next member premium −1:

    r_j(S_j)=s_j+1,
    r_(j+1)(S_j)=s_(j+1)−1.

At every other own-quitting coordinate set r_i(S)=s_i. Then λ_i=1 for
all i satisfies every coalition constraint with equality: the adjacent pair
premiums sum to zero, and all other participant premium sums are zero.

Peeling fails on A=I, because each i has a positive premium at {i,i+1}
contained in A. Thus no player ordering from the ordered-premium theorem
exists. This conclusion holds for EVERY passive completion.

One exact full passive completion, useful for distinguishing elementary
sources, is the following rule for i∉S:

    r_i(S)=s_i−1/2               if |S|=1,
    r_i(S)=s_i+2                 if S is an adjacent pair,
    r_i(S)=s_i−2                 if S is an opposite pair,
    r_i(S)=s_i+2                 if |S|=3.

Together with the own-coordinate rule this specifies all sixty Fin4 reward
entries and has |r_i(S)|≤3.

No pure sure-exit profile is Nash in this completion:

- from all-Continue, player 0 gains 1 by quitting;
- from singleton {j}, player j−1 gains 3/2 by joining;
- from adjacent pair {j,j+1}, its loser j+1 gains 1/2 by leaving;
- from an opposite pair, either outsider gains 2 by joining;
- from a triple, a member whose removal leaves an adjacent pair gains 2;
- from the grand coalition, any member gains 2 by leaving.

These are exact membership toggles, so they rule out all pure terminal Nash
laws. They do NOT imply a positive gap against mixed behavioral play; the
theorem supplies arbitrarily accurate equilibria for this table.

The old all-player weighted social chamber is also unavailable for ANY
nonzero nonnegative vector μ in this completion. At an adjacent row S_j,
the full weighted surplus over s is

    μ_j−μ_(j+1)+2Σ_(i∉S_j)μ_i.

Summing over j cancels the first terms and gives 4Σ_i μ_i>0. Thus some
terminal row violates the full weighted social bound for every such μ.
This distinguishes participant cancellation from cancellation of ALL player
rewards.

The existing affine-membership weighted-potential hypothesis is not
automatic either. For player 0 define g(T)=r_0(T∪{0})−r_0(T), with
r_0(∅)=0. This completion has

    g(∅)=1, g({1})=3/2, g({2})=1/2, g({1,2})=−2.

Affineness would require the last value to be 3/2+1/2−1=1, a
contradiction. The singleton solo-preemption graph also has both directions
between every pair, since all passive singleton payoffs are s_i−1/2.
These are separations from named source hypotheses, not from every existing
UE class or a worldwide novelty proof.

### 5.2 Ordered premiums with no positive cancellation weights

On Fin4 with the same s, start from r_i(S)=s_i for all S,i and change only
r_1({0,1}) to 1. The order 0,1,2,3 satisfies weak support peeling: the sole
positive premium requires earlier player 0. But the constraint at {0,1}
would be λ_1≤0. No strictly positive weight vector can satisfy (MP).

Thus the two finite reward classes are genuinely incomparable. Neither
example claims that its table lacks equilibrium by another route.

## 6. Strict positivity cannot be silently weakened

With three players and s=(1,0,0), start from r_i(S)=s_i and change the row
{1,2} to (2,1,1). The nonnegative but not strictly positive vector
λ=(1,0,0) satisfies every participant constraint, because player 0 has
no own premium. At q=(0,1,1), however, both active players have Q_i=1>s_i.
The root is exact against every continuation: each quitter loses by leaving,
and player 0 prefers its passive payoff 2 to joining for 1.

So nonnegative weights alone do not force an ACTIVE low-payoff quitter.
An inactive positive-weight coordinate cannot repair the averaging argument.
This is a failure of that weakened root premise, not a no-UE example.

## 7. Source comparison and mathematical status

The exact route was selected through `docs/TOOLKIT.md` and `docs/FRONTIER.md`.
The narrow current source check was at HEAD 98ea672; no Lean build was run.

- `Root/OpponentCoalitionPayoff.lean` contains
  `quittingRootQuitPayoff_eq_sum_opponentCoalitionMass`, the exact endpoint
  expansion underlying (1). The new weighted member summation is proved
  directly here, not assumed as an API field.
- `Root/NashExistence.lean` supplies `exists_isZeroQuittingRootNash`.
- The unit-only extraction and all-player fixed-payoff consumers are named
  in Sections 3--4. `Terminal/TerminalAffineReward.lean` already supplies
  `quittingTerminalPayoff_playerwiseAffine`, retaining the absorption
  correction in (5).
- `Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`
  contains `exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber`.
  Its reward bound sums ALL player coordinates, including passive ones.
  It is different from (MP), as the full completion above demonstrates.
- `Quitting/Stationary/ComponentwiseWeightedPotential.lean` requires
  `IsAffineQuittingMembershipGain` and
  `IsComponentwisePositiveSymmetrizable`. Its weights symmetrize membership
  influence coefficients; they do not express (MP).
- `math/notes/CODEX_EULER__POSITIVE_WELFARE_COMMON_NORMAL_SCREEN.md` concerns
  the same full-terminal-row social normal and its finite LP, not the
  participant-only sum in (1).

Paths abbreviated `Root/` and `Terminal/` are under
`UniformEquilibrium/Quitting/`; the diagnostics and stationary paths above
are under `UniformEquilibrium/`.

Original source: Solan and Vieille, *Quitting Games*, Mathematics of
Operations Research 26(2), 265--285 (2001), DOI
10.1287/moor.26.2.265.10549, especially Propositions 2.2--2.4 on printed
pp.270--272. The original local PDF and its relevant pages were inspected
in the preceding source audit; a narrow full-paper text search here did not
locate a weighted participant-premium condition. Proposition 2.2 already
states the low-payoff root hypothesis explicitly as weaker than capped
rewards. Thus the complete root/mesh/extraction mechanism is OLD; the present
candidate is the explicit finite weighted-table attachment.

The frozen [ordered-premium export](../exports/ORDERED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM.md)
(SHA-256 `a42680e45fe7a8a373337a624808eefee1fc5a3b53507eda32cb5a7e5e7f3b6e`)
preserves the same classical mechanism and its independent reviews. Its
ordered-table theorem is not invoked on a table that fails peeling. Rather,
identity (1) supplies the old conditional root premise independently.
`Literature/SolanAndVieille2001.lean` is a faithful but unbuilt literature
lane, not the production status of the new weighted adapter.

An exact Fraction calculation independently checked all sixteen pure
coalition toggles and all fifteen member-sum equalities of Section 5.1.
The equations and proofs above, not the calculation, establish the claim.

## 8. Bounded outcome and requested check

The proposed weighted route succeeds as a complete ordinary raw-table
producer with exact classes incomparable to ordered positive premiums.
The useful new identity includes λ_i q_i, not plain λ_i, and the unit
normalization transports weights by λ_i(s_i+t). Neither all-player welfare
bounds nor a joint payoff lottery appears.

The requested independent check is the all-root member identity, strict
positivity, weight transport at zero singletons, full-response consumer
composition, and the exact incomparability examples. No claim is made that
(MP) is necessary for the low-payoff-root condition or for equilibrium.
No common-box analytic barrier theorem is inferred for this weighted class.
