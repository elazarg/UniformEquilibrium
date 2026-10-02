# An asymmetric small-error kick and actual nonpivot-root amplification

Author: CODEX_TARSKI_PREMIUM.

Status: complete ordinary calculation on the known canonical VANISH table;
not independently reviewed, Lean-checked, or an export. The initially
tested exact-preservation grammar is STOPPED: its full root equations
force the already excluded equal-nonpivot-law format. Allowing a single
arbitrarily small ORIGINAL nonpivot error removes that invariance. The
explicit asymmetric kick and subsequent actual root choices below turn
the bad finite-menu Nash source into finite laws of arbitrarily small
unrestricted regret. This is a source-deformation calibration, NOT a new
UE class or an arbitrary-table producer. Section 6 isolates the raw signs
used and the genuinely missing arbitrary-table step.

## 1. Operation on actual finite sources

The target is the current
[single-pivot finite-menu question](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md):
s=(1,0,0,0), zero Never, arbitrary other bounded real rewards, independent
stopping laws, and all complete behavioral deviations. For a finite law
p on F_N write U_i, full cap B_i, and d_i=B_i−U_i. Canonical finite-menu
Nash supplies d_j=0 for all j>0; it need not control d_0.

Fix a pivot head probability z∈[0,1]. Regard its Bernoulli action as fixed
and solve the THREE nonpivot root best-response equations at their actual
continuation payoffs U_j. This is an ordinary finite three-player game,
so its equilibrium set is nonempty. The full graph over all z is closed
and compact. No continuous selector, selected component, or assumption
that the pivot best responds is used. Prefix any resulting product root
q=(z,q_1,q_2,q_3) to the SAME actual tail p.

Let Q_i be the immediate Quit endpoint, A_i the immediate-absorption
contribution when i Continues, and α_i the probability all its opponents
Continue at the root. Then

    C_i(U)=A_i+α_i U_i,
    U'_i=q_i Q_i+(1−q_i)C_i(U),
    B'_i=max(Q_i,A_i+α_i B_i).                          (1)

These are unrestricted caps: a deviator chooses its first action and,
on the deleted-player survival branch, an arbitrary complete tail law.
Taking suprema proves (1) without assuming a cap is attained. Never,
every joining action, and every shifted/omitted deadline are included.

For a nonpivot root best response, with G_j=Q_j−C_j(U),

    d'_j=[α_j d_j−max(0,G_j)]_+ ≤d_j.                  (2)

Thus exact zero debts remain zero; more importantly, existing original
errors at most δ remain at most δ. The pivot's exact comparison is

    d'_0=max(Q_0,A_0+α_0 B_0)
      −z Q_0−(1−z)(A_0+α_0 U_0).                     (3)

For a finite source the new law is finite on F_(N+1). Formula (3), not
the root's two-action Nash error, is the objective being tested.

This is not exact cap-Nash prefixing: only three players optimize, at
U_j rather than a freely supplied continuation, and z is independently
reselected over its WHOLE interval. Equations (1)–(2) themselves are
existing prefix arithmetic, not the new producer. The canonical zeros
are used to obtain three FULL small-debt coordinates from a finite-menu
source; they are not needed for the abstract cap identity.

## 2. Complete raw calibration and actual bad source

Use the already solved VANISH table, with cyclic predecessor i⁻ and
successor i⁺ on {1,2,3}:

    r_0(S)=1 if 0∈S, and 2 otherwise;
    r_i(S)=0 if i∈S;
           −1 if i∉S and 0∈S;
           2·1_(i⁻∈S)−1_(i⁺∈S) otherwise, i>0.

This specifies all fifteen terminal rows. Its singleton vector is exactly
(1,0,0,0), and |r_i(S)|≤2. In particular the nonpivot participating
rewards vanish for ALL coalitions, a stronger property than zero own
singletons. It will be used explicitly.

Put x=1−2^(−1/3), y=x/(1+x). The one-date profile p* has pivot Quit
probability y, each nonpivot Quit probability x, and Never otherwise.
Its complete finite-menu comparisons are Q_0=C_0=1 and Q_j=C_j=0.
Every nonpivot late response agrees with Never, and the pivot's late
response is 1+(1−x)^3=3/2. Therefore

    U(p*)=(1,0,0,0),      B(p*)=(3/2,0,0,0).           (4)

This is an ACTUAL finite-menu Nash source with E=1/2, not an externally
supplied small-total-debt seed. The prior canonical separation note
proves that it is the unique exact finite-menu Nash law up to its last
date at every positive deadline; uniqueness is not needed below.

## 3. Why preserving the exact zero face cannot be the producer

If U_1=U_2=U_3=0, the three induced root Continue endpoints are

    C_i=−z+(1−z)(2q_(i⁻)−q_(i⁺)),       Q_i=0.

The COMPLETE equilibrium set consists of the single triple

    q_i=z/(1−z) for 0≤z≤1/2;
    q_i=1       for 1/2≤z≤1.                           (5)

Here is the boundary check. At z=0 the usual maximum-coordinate argument
forces q=0: a maximal positive q_i makes its successor Continue strictly,
then the other two root inequalities force an impossible sure Quit.
For 0<z<1 set t=z/(1−z). A zero coordinate would force its successor
to one and its predecessor to at least (1+t)/2. For t>1 this is
impossible; for t≤1 that predecessor instead strictly prefers Continue.
Thus no coordinate is zero. When t<1, a coordinate equal to one forces
its successor to zero; all coordinates are consequently interior and
2q_(i⁻)−q_(i⁺)=t has the unique solution q_i=t. For t≥1 an interior-only
solution is impossible. One sure coordinate and two interior coordinates
would force one interior coordinate to (1+t)/2>1; two sure coordinates
force the third sure. At t=1 the same inequalities force all three to
one. At z=1 all three strictly prefer Quit. This proves (5), including
the degenerate endpoint, without selecting a favorable branch.

Every such root preserves all three continuation payoffs at zero.
Starting from (4), it therefore preserves equal nonpivot clock laws
under EVERY finite word, however z is reselected. The existing
[all-symmetric-law obstruction](../notes/CODEX_RENY__SYMMETRY_PRESERVING_LOGIT_SELECTOR_OBSTRUCTION.md)
already bounds every resulting profile away from zero full regret.
The new method-specific fact is the forced invariance (5), not another
general symmetry obstruction.

For an exact arithmetic check, set a=2−B_0, d=B_0−U_0. Initially a=d=1/2.
For z≤1/2 put α=((1−2z)/(1−z))^3. The entire full-cap recurrence is

    a'=αa,       d'=z+α[(1−z)d−az].                    (6)

For z≥1/2 it is a'=0, d'=z. The invariant 0≤a≤1/2, d≥1/8 follows:
at the adverse boundary a=1/2,d=1/8, the increase in d is

    z²(32z²−43z+15)/(8(1−z)^3) ≥0

on [0,1/2]; the quadratic is decreasing there and is positive at 1/2.
This is a bounded check of the already excluded format, not a new gate.

Even greedy full-interval optimization can stop at an actual finite
source. One hundred prefixes with z=1/100 give

    a=(941192/970299)^100/2 >23/1000,
    v:=2−U_0=9801/38908
          +(29107/38908)(235298/245025)^100 <267/1000.

Both inequalities are exact integer comparisons. Hence 1+3a−4v>0.
For ANY source on this face with v≤(1+3a)/4, (6) cannot lower d=v−a:
the difference is minimized at v=(1+3a)/4, where it equals

    z²[(1−z)(3−4z)+a(24z²−29z+9)]/(4(1−z)^3)>0

for 0<z≤1/2. The second quadratic has negative discriminant and is
positive. For z≥1/2, d'=z≥1/2 while d≤1/4. At z=0 nothing changes.
This remains a RESTRICTED source, not a positive global E minimum.

## 4. An arbitrarily small ORIGINAL-error asymmetric kick

Now allow the small nonpivot errors permitted by the actual question.
Fix 0<δ≤1/4 and prefix to p* the root (0,δ,0,0): only player 1 may
Quit. Direct use of (1), including each joining alternative, gives

    U=(1+δ,0,2δ,−δ),
    B=(3/2+δ/2,0,2δ,0),
    d=( (1−δ)/2,0,0,δ).                               (7)

This root is intentionally NOT nonpivot Nash: its small original debt
δ is the resource allowing the law asymmetry. It is not a private bonus,
an auxiliary payoff modification, or a small-TOTAL-regret seed.

At the actual continuation (7), prefix the root

    q_0=q_1=0,       q_2=δ/(2+δ),
    q_3=2δ/(1+2δ).                                    (8)

All participating nonpivot endpoints are zero. The Continue endpoints
for players 2 and 3 are respectively

    2δ−(1+2δ)q_3=0,
    −δ+(2+δ)q_2=0.

Player 1 strictly prefers Continue, whose value is

    v_0=2q_3−q_2
       =δ(7+2δ)/[(1+2δ)(2+δ)] ∈(0,1).                (9)

Thus (8) is a genuine induced nonpivot equilibrium, and the new
nonpivot payoff vector is (v_0,0,0). Equation (2) retains all three
FULL debts at most δ; more exactly only player 3 can have debt, namely
δ(1−q_2). No conditional-reach division or cap compression is involved.

For the pivot, U_0≥1 and B_0≥1 throughout this construction. Its Quit
endpoint is always 1. With q_0=0 its Continue payoff and cap are
2(1−α_0)+α_0 U_0 and 2(1−α_0)+α_0 B_0 respectively, both at least 1.
Consequently its full debt after (8) is exactly α_0 times its previous
debt, and is at most 1/2.

## 5. Exact rotating amplification and full finite output

Suppose the current nonpivot payoffs have a single positive coordinate
v∈(0,1), at player k, and the other two are zero. Let j=k⁺ and let l
be the remaining nonpivot. Prefix a SOLO-j root of probability

    q=v/(1+v),        with the pivot always Continuing.

Player j is indifferent at value zero. Player k's Continue payoff is
(1−q)v−q=0, matching its zero joining value. Player l gets 2q>0 from
Continue and zero from joining. These are all three nonpivot root
inequalities. The new positive coordinate is at l and equals

    v'=2v/(1+v),       0<v<v'<1.                       (10)

Every nonpivot full debt stays at most δ by (2). Independently, the
pivot cap calculation at the end of Section 4 gives

    d'_0=(1−q)d_0=d_0/(1+v).                          (11)

There is no transfer of a prescribed-payoff identity to a cap: (11)
follows by explicitly checking which of the two unrestricted cap
endpoints is larger. Arbitrary late pivot responses and all three
nonpivot joining/deadline tests are still included.

After K such rotations, (10) telescopes:

    ∏_(k<K) 1/(1+v_k)=v_K/(2^K v_0)≤1/(2^K v_0),
    d_0≤1/(2^(K+1)v_0),       max_(j>0)d_j≤δ.          (12)

Given ε>0 choose δ=min(ε,1/4), then K with 2^K v_0≥1/(2ε).
The resulting literal independent law on F_(K+3) has full E≤ε, hence
both E_(K+3)≤ε and L_0≤ε. All choices precede the final verification;
the sole initial seed is the explicit bad Nash source (4). Payoff
targets are allowed to change. No infinite-tail absorption assumption
is transferred to the finite word. Known same-table UE existence is
not counted again as a new class result.

## 6. What is automatic, what is extra, and the next actual-source test

There are TWO different mechanisms in the calculation.

First, rotating expansion uses the cyclic passive rewards −1 and 2,
zero joining rewards for the adversely affected nonpivot, and a joining
reward no greater than the passive benefit for the beneficiary. More
generally a negative passive entry −b and positive entry g give the
solo update v↦gv/(b+v), whose small-value expansion factor is g/b.
A three-cycle needs a product of such expansion factors exceeding one.
These signs and joining inequalities are NOT supplied by s=(1,0,0,0).
The two-active repair (8) additionally uses its literal pair collision
rewards; singleton matrix data alone do not justify its equations.

Second, pivot contraction uses B_0≥1 and the endpoint comparison

    (1−q)·1+q r_0({0,j})
       ≤(1−q)B_0+q r_0({j}).                          (13)

VANISH has r_0({0,j})=1 and r_0({j})=2. This is why (11) holds.
Equation (13) is not implied by the nonpivot expansion factor. Actual
punishment normality P_0≤1 is an upper bound on a min-max value, not
the lower bound B_0≥1 at an arbitrary selected source. Neither the
canonical normalization nor the no-UE raw blockers supply the displayed
full set of collision and endpoint signs on a nonpivot-only cycle.

There is a stronger prior matrix-class overlap than just the known
canonical cyclic construction. In the row convention
Γ_ij=r_i({j})−s_i, the normalized singleton matrix is

    Γ = [ 0  1  1  1 ]
        [−1  0 −1  2 ]
        [−1  2  0 −1 ]
        [−1 −1  2  0 ].

For every x≥0, xᵀΓx=x_1x_2+x_1x_3+x_2x_3≥0. Every principal is
therefore copositive. On each principal, either the homogeneous simplex
branch holds, or R₀ plus copositivity gives standard Q; either case gives
projective Q. Thus Γ is projective Q-bar, consumed by the existing
unconditional `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell`.
This covers EVERY collision-table completion with these singleton rows,
not just this calibration's particular participating rewards. Its matrix
already lies outside the genuine no-UE residual.

On the other hand it is not a weak-subset-exclusion calibration: pivot Never
and three independent one-date hazards 1/2 give actual payoff
(7/4,1/4,1/4,1/4), strictly above all four singletons. No broad new
matrix-class coverage claim is made.

The meaningful next question is whether, outside the already solved
matrix/cycle exits, raw data allow selection of SOME actual finite source
and a small asymmetric original-error kick whose actual nonpivot
continuation roots allow unbounded cumulative OPPONENT absorption while
retaining the pivot endpoint comparison. The selected source may change
with accuracy. Repair of EVERY supplied finite-menu Nash law, preservation
of its target, or transport of one selected equilibrium is not required
by the original question. A favorable positive continuation is not an input.
The canonical identities supply three initial full error bounds only;
they do not supply that expansion or endpoint sign. This is the exact
missing implication, not an established compatible-family theorem.

## 7. Source and scope record

The source route was `docs/TOOLKIT.md` →
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar` and
`singlePivot_nonpivot_fullDebt_eq_menuDebt`, in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
The finite timing game/behavior adapters and
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` were read. The
existing coordinate prefix budget is
`quittingTerminalSemanticDebt_prefix_le_auxiliaryNashDefect`, in
`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`.
Finite root existence is recorded by `exists_isZeroQuittingRootNash`,
in `UniformEquilibrium/Quitting/Root/NashExistence.lean`; the induced
three-player game here is obtained by fixing the pivot's Bernoulli action.

For the matrix-class comparison, the exact declarations inspected are
`isR0Matrix_iff_not_singletonLCPFeasible` and
`copositive_isR0Matrix_isStandardQ` in
`MathUE/LinearProgramming/CopositiveQ.lean`,
`isStandardQMatrix_of_copositive_of_isR0Matrix` in
`UniformEquilibrium/Quitting/Classification/LCP/CopositiveQBridge.lean`,
`isProjectiveQMatrix_iff_standard_or_homogeneous` and
`IsProjectiveQBarMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`, and
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
`UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.
The source-only blockers were compared with
`exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform` in
`UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`;
they do not provide the cycle/collision signs used above.

The complete canonical table/source and known successful finite cycle
come from
[CODEX_RENY's canonical separation](../notes/CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md).
The earlier planned-Never bonus selection in
[CODEX_HILBERT](../notes/CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR.md)
also succeeds on this solved table, but changes a synthesis objective;
(7) instead changes the actual law and pays its original error explicitly.
The whole-pivot repair/finite-response coupling of
[CODEX_RENY](../notes/CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md)
is not assumed to select or preserve these root words.

The global/restricted distinction is mandatory. The
[MAX tie/root-uniqueness result](../notes/CODEX_RENY__MAXIMUM_DEBT_MINIMUM_TIES_AND_ACTUAL_ROOT_UNIQUENESS.md)
and
[finite-menu/global-minimum separation](../notes/CODEX_NOETHER_SUPPORT__FINITE_MENU_NASH_AND_GLOBAL_MAX_MINIMUM_SEPARATION.md)
already prevent identifying a positive one-debtor infimum with the true
global full-regret minimum, including nonattainment. VANISH's global
infimum is zero. None of Sections 3–5 gives a new necessary condition
on a genuine positive global infimum.

Exact rational checks verified the six root regimes z=0,1/100,1/4,1/2,
3/4,1, the two integer inequalities in Section 3, and its invariant
polynomial on a 101-point grid. An independent coalition enumerator
computed BOTH endpoints of every full cap for 496 rational values
δ=a/b∈(0,1/4], 4≤b≤64, through the kick, repair, and nine rotations each.
It verified (7)–(12), every nonpivot root inequality after the kick, and
the exact surviving player-3 debt after repair. The complete statements
use the displayed ordinary all-parameter proofs, not these finite checks.
