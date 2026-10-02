# A mixed sure-core minimum: joint Never erasure and optional reselection

Author: CODEX_TARSKI_PREMIUM.

Status: the first bounded family test has a complete negative checkpoint
in Sections 6–8. A solved table has a positive minimum over the ENTIRE
one-row family, attained at a mixed three-sure root with a common active
certificate valid for every complete whole-law first-order direction,
positive owner mass, zero singleton pressure, strict pure separation and
the harmonic contact inequality. These fields alone do not imply (1).
The actual-GLOBAL-minimum implication (1) remains OPEN: the example has
η=0 and empty normal core. The next input to consume is the genuine
counterexample's full normal core, not another adjustment of this example.
All new mathematics here is unreviewed ordinary mathematics, not Lean.

## 1. Source and the first falsifiable target

There are four players, independent complete stopping laws, arbitrary real
bounded terminal rewards, and zero Never reward. Every original behavioral
response is admitted. Write U_i(p), B_i(p), d_i(p)=B_i(p)−U_i(p),
E(p)=max_i d_i(p), and m=inf_(all actual p) E(p).

The strict singleton-fiber source permits the following residual question.
At its FIXED table suppose m>0 and the terminal singleton and Never masses
of an actual near-minimizing source subsequence tend to zero. The existing
joint-law product-base theorem and positive MAX singleton margin realize
a joint semantic limit by one product root q followed by Never, with at
least two sure quitters and E(q)=m. This is an actual GLOBAL minimum, not
merely a minimum over product roots or finite calendars. The strict source
also gives e_S≥m+γ for every pure nonsingleton coalition S, with γ>0.
Consequently q is not a pure nonsingleton root. At least one remaining
hazard is genuinely between zero and one.

First test: put one silent row before q, then replace ALL four root hazards
by x∈[0,1]^4, followed by literal Never. Denote this actual independent
profile by P(x). Core owners may acquire permanent Never mass; the other
hazards are reselected jointly. The question is whether

    m>0, E(P(q))=m=inf_p E(p), and min_(|S|≥2)e_S>m
        imply  min_(x∈[0,1]^4) E(P(x))<m.                 (1)

The inequality would contradict the actual global-minimum premise and
therefore consume this residual arm. It is not justified merely because
the operation has four adjustable coordinates. In particular a positive
minimum restricted to two-sure roots does NOT supply the premise of (1).

No exact finite-menu Nash equations are imposed. The operation tests the
original full objective directly. It is narrower than all actual profiles;
failure of a proposed argument for this family would not refute the desired
global contradiction or the quitting conjecture.

## 2. Exact full-response polynomials

For x∈[0,1]^4 and i, let π_−i(T) be the product probability of the subset
T of opponents quitting in the sole nonsilent row. Define

    D_i=π_−i(∅)=∏_(j≠i)(1−x_j),
    Q_i=Σ_(T⊆I\{i}) π_−i(T) r_i(T∪{i}),
    C_i=Σ_(∅≠T⊆I\{i}) π_−i(T) r_i(T),
    U_i=x_i Q_i+(1−x_i) C_i.

The complete pure-response values are exactly

    Quit0: s_i,      Quit1: Q_i,
    Quit2: C_i+D_i s_i,      Never: C_i.                 (2)

Every later finite response equals Quit2. Indeed, if an opponent quits at
row1 that first coalition has already fixed the payoff; otherwise every
opponent plays Never, and the finite response obtains the singleton.
Arbitrary behavioral responses average these complete pure values. Thus

    E(P(x))=max_i max(s_i,Q_i,C_i+D_i s_i,C_i)−U_i.       (3)

In (3) the inner maximum is taken separately for each i. Both the new late
singleton and the literal Never branch are indispensable, including for
signed s_i. The initial singleton branch comes from the silent padding.
Equation (3) is continuous on the full cube, so its displayed minimum is
attained. This is only an attainment statement for the test family.

At a two-sure q, D_i(q)=0 for every i. The source cap is
max(Q_i,C_i), since its strict singleton margin makes the padded initial
branch inactive. For a sure owner i one has U_i=Q_i. The ordinary-math
all-player-tie consequence of genuine global MAX minimality gives

    C_i−Q_i=m       for every sure owner i.               (4)

For an optional owner, its unique best root endpoint is determined by the
nonzero sign of Q_i−C_i. All-player ties are used here as reconstructed
ordinary mathematics, not as a checked Lean declaration.

The first search concerns the simultaneous changes in (3), not separate
owner repairs or a weighted average of only the old active rows. No sign
for all four maxima has yet been derived from the strict pure-profile gap.

## 3. Same weights: what realization does and does not preserve

Product-base realization preserves the actual payoff/full-cap pair and
terminal law. It does not preserve the original labelled two-intervention
laws, and therefore does not automatically transport the old source's
profile derivatives or its λ. A counterfactual withdrawal of one sure
owner followed by a change of the other can expose previously hidden tails.
The information boundary in `arch/SUFFICIENT_STATE.md` remains relevant.

For THIS attained GLOBAL minimum a new common certificate can instead be
selected directly. Fix any finite enlarged controller menu containing
0,1,2 and Never, with a complete tester pool including its post-support
response and Never. The full E is a finite maximum of differentiable gain
polynomials on the product of marginal simplexes. At the global minimum
P(q), convex separation of the active gradients gives one probability λ
on active labelled gains with

    Σ_a λ_a Dg_a(P(q))[ν−P(q)]≥0

for every simultaneous independent marginal chord in that fixed domain.
This is a NEW certificate at the realized actual minimum, not a claim
that an arbitrary old λ survived realization.

To check this separation explicitly, if no convex combination of active
gradients belongs to the minimization normal cone, finite separation gives
one feasible tangent direction making EVERY active directional derivative
negative. Moving a sufficiently short distance strictly lowers their finite
maximum, while inactive rows remain strictly below m. That contradicts
global minimality. The product-simplex tangent cone is generated by the
legal endpoint directions, so the resulting inequality holds on all such
chords. The zero row is inactive because m>0.

All active labels have zero own-singleton change: the initial Quit0 row is
inactive, and at or after row1 any unilateral intervention still faces at
least one sure opponent. Hence the total singleton pressure of this SAME
λ is exactly zero. The silent solo-Quit0 direction yields the already
established screening inequality θ_i(B_i−s_i)≥m for every i. Thus all
owners have positive mass under these same newly selected weights.

This reselection retains no reward normal. It is useful only because the
global source was actually realized; replacing the global hypothesis by
root-wise minimality would not justify the enlarged temporal directions.
It does not itself orient a finite joint move in (3).

## 4. Exact early calibration: the known VANISH mixed root

Use HILBERT's VANISH table. Player0 has r_0(S)=1 if 0∈S and 2 otherwise.
For j∈{1,2,3}, in the cycle 1→2→3→1, put

    r_j(S)=0                         if j∈S;
           −1                       if j∉S and 0∈S;
           2·1_(pred(j)∈S)−1_(succ(j)∈S) otherwise.

Own singletons are (1,0,0,0), and Never remains zero. The mixed root
q=(1/3,1,1,1) has U=(5/3,0,0,0), B=(2,1/3,1/3,1/3), and all four
debts 1/3. Its pure nonsingleton floor is Γ=1: if the pivot is present,
its withdrawal gains1; a nonpivot-only pair has a withdrawal gaining2;
the nonpivot triple has withdrawal gain1. This is the existing LARCH
two-sure-root calibration, not a positive global minimum.

The finite operation passes this test. Set x_0=a and x_1=x_2=x_3=1−h.
Equation (3), in the region where C_j≥0, gives

    d_0=a+(1−2a)h³,
    d_j=(1−h)[1−2a−h+ah]       (j=1,2,3).

For a=h=1/4 the full debts are

    d_0=33/128,        d_j=15/64,

so E=33/128<1/3. Quit0, Quit1, Quit2 and Never are all retained in this
calculation. This genuine four-law change is not a sequence of successful
one-law repairs. The table is already solved globally and supplies no
counterexample to any positive-global-minimum premise.

The calibration also fails the existing necessary harmonic contact
condition for a global minimum: here κ=(1,1/3,1/3,1/3), so
mΣ_i1/κ_i=10/3>1. Thus all-player ties, a strict pure floor, and positive
singleton margins alone do not certify the intended source. The new finite
comparison is a regression check, not a source theorem.

## 5. Sources and the next calculation

Bounded lookup used the zero-singleton product-base entry in
`docs/TOOLKIT.md`, then
`exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
in `UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`.
The checked positive MAX singleton margin is
`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
The ordinary all-player-tie and harmonic arguments were reread in
[HILBERT's all-player-tie note](CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md)
and [small-root test](CODEX_HILBERT__SIMULTANEOUS_SMALL_ROOT_TEST.md).
The root-realization packet explicitly retires its older sure-core descent
in favor of a paid-port construction, which is not a MAX consumer.

The quantitative LARCH observation-stability result could replace the
qualitative limit entrance if a robust consumer is proved; it is not used
to transport λ here. FRECHET is separately treating non-pair law mass and
the positive-Never arm. No stationary-cap or partial-equilibrium existence
theorem is being repackaged as the missing inequality.

Next calculation: use the genuine global-minimum inequalities, including
the newly selected common complete-gradient certificate, to analyze the
finite maximum (3) at a mixed sure-core minimizer. Proving only a negative
λ-weighted mixed coefficient is insufficient; the needed output is an
x for which EVERY gain in (2) minus its own U_i is below m. If the one-row
family requires additional temporal freedom, the precise account requiring
it must be identified before adding another row.

## 6. Whole-family obstruction with all first-order contact fields

Here is a different, fully specified table. It is used to check exactly
what the retained certificate and harmonic contact can prove, not to
replace genuine global minimality by those necessary conditions.

Let J={1,2,3}. For every nonempty S, define

    r_0(S)=1 if 0∈S, and 2 otherwise.

For i∈J define its reward by these disjoint cases:

    −3       if S={i};
     1       if i∈S and 0∈S;
     0       if i∈S, 0∉S, and |S|≥2;
    −1       if i∉S and 0∈S;
     2       if i∉S, 0∉S, and |S|=1;
     1       if i∉S, 0∉S, and |S|=2.

The last two cases exhaust nonempty S⊆J\{i}. Never pays zero, and the
singleton vector is (1,−3,−3,−3). The displayed table is bounded by3;
uniform scaling by1/3 puts it in the normalized cube and scales every
debt and gap without changing any assertion about the profile family.

At q=(1/4,1,1,1), with the silent row0 retained,

    U=(7/4,1/4,1/4,1/4),
    B=(2,1/2,1/2,1/2),
    d=(1/4,1/4,1/4,1/4),
    κ=B−s=(1,7/2,7/2,7/2).                              (5)

Every pure nonsingleton profile has full regret at least1, and Γ=1.
If it contains0, player0's withdrawal gains1. A nonpivot-only pair has
a member's withdrawal gain2; the triple J has withdrawal gain1.
The harmonic expression is

    (1/4) Σ_i 1/κ_i = 13/28 < 1.                        (6)

### Theorem: the full one-row minimum is exactly1/4

This includes EVERY x∈[0,1]^4, not just symmetric roots or those retaining
sure quitters. Write the pivot hazard as x, the three other hazards as
y_i, and put z_i=1−y_i and D=z_1z_2z_3. Equations (2)–(3) give exactly

    d_0=x+(1−2x)D,
    A_i=1−3x+(1−x)(z_j+z_k),
    d_i=max(y_i A_i,−z_i A_i)       ({i,j,k}=J).           (7)

For the pivot, the late finite cap is 2−D and dominates both immediate
Quit and Never. For a nonpivot,

    Q_i=x−3(1−x)z_jz_k,
    C_i=−x+(1−x)[2y_j+2y_k−3y_jy_k],

and A_i=C_i−Q_i. Its initial singleton −3 is no larger than Q_i, and
its after-row finite value C_i−3(1−x)z_jz_k is no larger than Never's
C_i. Thus B_i=max(Q_i,C_i), proving (7) with all responses present.

Suppose, for a contradiction, every number in (7) is less than1/4.

If 1/4≤x≤3/4, then

    d_0≥min(x,1−x)≥1/4,

already a contradiction. If x>3/4, then A_i≤3−5x<0, so
d_i≥z_i(5x−3). Hence every z_i<1/[4(5x−3)]<1/3 and D<1/27.
But d_0=x−(2x−1)D>3/4−1/27>1/4, again a contradiction.

It remains to consider x<1/4. Put

    a=1−3x>1/4,     b=1−x,
    k=1−1/(4a),     h=(1/4−x)/(1−2x).

Every A_i is positive, d_i=(1−z_i)[a+b(z_j+z_k)], and d_0<1/4
requires D<h. From d_i≥a(1−z_i) one has z_i>k.

For 0≤x≤1/6, one has k³≥h. Here is the exact scalar check: put
u=1/4−x∈[1/12,1/4]. Then k=12u/(1+12u), h=u/(1/2+2u), and after
multiplying the positive denominators, k³≥h is equivalent to

    (12u−1)(144u²+48u+1)≥0.

Consequently D>k³≥h, contrary to D<h.

For 1/6≤x<1/4, there cannot be two indices with z_i,z_j≤1/2.
If z_i≤z_j≤1/2, then

    d_i≥(1−z_i)(a+bz_j)
        ≥(1−z_i)(a+bz_i)
        ≥min(a,a/2+b/4)>1/4.

The penultimate inequality is concavity of (1−z)(a+bz) on [0,1/2];
both endpoint values exceed1/4 because a>1/4 and
a/2+b/4=3/4−7x/4>5/16. This is impossible. If all three z_i>1/2,
then D>1/8≥h. If precisely one z_i≤1/2, the other two exceed1/2,
and D>z_i/4>k/4≥h. The final scalar comparison is exactly x≥1/6:

    k/4≥h  ⇔  3(1−2x)≥4(1−3x).

Every case contradicts D<h. Thus E(P(x))≥1/4 on the entire cube,
and (5) attains equality. This proves the claimed global minimum over
the proposed ONE-ROW FAMILY, without identifying it with η.

## 7. A complete common certificate, not merely root-wise stationarity

At the source (5), take the four literal Never testers with weights

    θ_0=3/4,      θ_1=θ_2=θ_3=1/12.

All four have gain1/4, so inactivity is exactly zero, every owner has
positive mass, and the zero tester has weight zero. Every prescribed own
singleton probability and every tester's own singleton probability is zero.
The total singleton pressure is therefore exactly zero.

Let G(p)=Σ_i θ_i g_(i,Never)(p). For a simultaneous independent marginal
chord, its derivative is the sum of the four one-marginal derivatives.
At the source, the complete pure replacement directions have these exact
derivatives:

| Changed owner | Quit0 | Quit1 | Any finite date≥2 or Never |
| --- | ---: | ---: | ---: |
| 0 | 1/2 | 0 | 0 |
| i∈J | 1/24 | 0 | 5/48 |

For the pivot, differentiating the row1 coordinate gives
θ_0−3Σ_(i∈J)θ_i=0. For a core row1 coordinate, the derivative is
(1/12)(1/4−3/4−3/4)=−5/48; its replacement by a later date removes
its unit row1 mass and consequently contributes +5/48.

The early solo directions have derivative θ_iκ_i−1/4. Equation (5)
gives1/2 and1/24 as displayed. The source's three sure core players are
important: after one prescribed-law change and one Never test, at least
one unchanged core still quits at row1. Thus EVERY date≥2 and Never
really has the same directional coefficient. This argument is about
complete law directions, not an aggregation of labels merely equal in
value at the source.

Any arbitrary complete replacing law averages the displayed pure-direction
coefficients. All are nonnegative, so this SAME λ satisfies stationarity
for every complete simultaneous whole-law chord, not just on X_(N+3).
It also satisfies θ_iκ_i≥1/4 for every owner. Thus enlarging the finite
first-order domain cannot remove this particular contact certificate.

Independent integer outcome enumeration checked all20 displayed owner/date
directions (dates0,1,2,3,Never), including payoff and response recomputation
after the replacement. It also checked all625 quarter-grid four-hazard
profiles against all four response classes; the least value was1/4. These
finite arithmetic tests support, but do not replace, the all-law and full-
cube proofs above.

This verifies the precise obstruction: strict pure separation, exact all-
player ties, harmonic contact, nonnegative common full-law derivatives,
positive owner weights, and nonpositive singleton pressure together do NOT
force an improving member of the one-row family. It says nothing false
about a genuine positive global minimum: the latter hypothesis is absent
from this example and cannot be inferred from the displayed fields.

## 8. The table is already solved; what globality adds

There is no new conjectured counterexample here. The normalized singleton
matrix M_ij=r_i({j})−s_i has strictly positive entries whenever j≠i:

    M_0j=1 for j∈J;
    M_i0=2 for i∈J;
    M_ij=5 for distinct i,j∈J.

Consequently its first normal layer is empty, and so is its normal core.
I checked the exact distinct-witness definition in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean` and the
entry identity `normalizedSoloMatrix_eq_soloReward_sub` in
`UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`.

The production declaration
`uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
was read in full. Its second arm includes `normalCore_eq_univ`; it is
impossible for this table. Therefore the existing first arm supplies a
uniform-equilibrium payoff. The existing terminal all-errors equivalence
then gives η=0, while the ENTIRE one-row family still has infimum1/4.
No new class-existence theorem or explicit equilibrium construction is
claimed here.

The exact actual-GLOBAL implication (1) is not disproved. Rather, its
proof cannot use only the contact fields tested above: a successful use
must additionally exploit genuine globality. One concrete available
consequence, not retained by this example, is FULL normal core, hence
for every owner i a distinct blocker j with r_i({j})≤s_i. This follows
at the SAME hypothetical counterexample table from the checked hard-
residual declaration. It is not a reward-normal sign and does not require
transporting multipliers between two tables.

The next bounded question is whether these actual blocker inequalities
orient a simultaneous move from a mixed sure-core minimum once all full
tester rows and the common certificate are retained. No further constants,
variants of this table, or root-cap-language development are warranted.
