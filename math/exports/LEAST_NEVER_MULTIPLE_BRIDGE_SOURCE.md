# Least literal Never forces two bridging owners or a later-only owner

## Exact theorem and scope

This is a self-contained ordinary mathematical source reduction, NOT
a Lean-checked theorem or a uniform-equilibrium producer.

From ANY finite four-player quitting game lacking a uniform-equilibrium
payoff, the proof selects ONE fresh table r†, then performs only
same-table selection and actual independent-law variations. Its table
r† lies in [−1,1]⁶⁰ and has distinct nonempty entries within each
recipient row. At r†:

    0<δ=Δ_all(r†)<Δ_abs(r†)=δ+g,
    all own singleton rewards s_i are positive,
    all full minima share a strictly positive debt vector d*.

Select the LEAST literal joint-Never probability among its full
minima, retaining that coordinate in the actual augmented carrier.
Every produced marked representative of this selection has the
nonsure atomic first root τ supplied in Part I, and either:

    (I) at least TWO DIFFERENT owners maximize both at τ and later;

    (II) exactly ONE owner i maximizes at τ and later, its original
         root rate is zero, and some DIFFERENT owner has its ENTIRE
         maximizing response set strictly later than τ.

All later responses are finite compact clock points with actual moving
FINITE-deadline witnesses. Root/later bridging kernels differ on a
positive original opponent-root event. Multiple labels for one owner,
or payoff-equivalent labels, are not counted as two bridging owners.
All four debts and literal joint Never remain positive. The table,
global full minimum, absorbing gap and unrestricted response class are
common to this ONE selected source.

The theorem is exhaustive at this selected source, not a supplied-object
verifier. It does not claim that every old minimum obeys the disjunction,
that a raw integer-clock minimizer exists, or that either residual
alternative has an equilibrium consumer. The full Fin4 conjecture
remains open.

Part I proves the complete original counterexample source; Part II
proves the added end-wall, old-law and least-literal-Never steps.
No proof depends on a conference note or packet. Only the explicitly
named tracked Lean declarations serve as external mathematical inputs.

## Part I: complete fully-paid nonsure counterexample source

### 1. Exact theorem and the whole-game improvement

This is ordinary mathematics, not a Lean-checked theorem. It is an
actual-counterexample source reduction, not a uniform-equilibrium
producer. All compact/source and signed-variation inputs not supplied
by tracked declarations are proved below.

Let I={0,1,2,3}. A finite signed table r specifies r_i(S) for
every recipient i and nonempty S⊆I. Terminal AllNever pays0.
Each player privately chooses an independent complete stopping law
on ℕ⊔{Never}, equivalent to unrestricted behavioral play in the
original Boolean quitting game. The first finite tied coalition
determines terminal rewards. A unilateral deviation replaces the
owner's ENTIRE law. Its full cap includes EVERY pure finite
deadline and literal Never, hence ALL behavioral deviations.

For an actual profile p define prescribed payoffs U_i(p), full
response caps B_i(p), debts d_i=B_i−U_i≥0 and D(p)=Σ_i d_i.
Let P_all be all actual law profiles and P_abs those whose play
absorbs almost surely. Independence means p∈P_abs exactly when
ν(p)=∏_i p_i(Never)=0. Write K_all,K_abs for the closures in ℝ⁸
of the ENTIRE actual payoff/cap pairs from these respective
classes, and

    Δ_all(r)=min_(K_all)D=inf_(P_all)D,
    Δ_abs(r)=min_(K_abs)D=inf_(P_abs)D.

These nonempty compact carriers are not sets of necessarily
attained raw-integer profiles.

If ANY Fin4 quitting game has no uniform-equilibrium payoff, there
exists ONE table r†∈[−1,1]⁶⁰ with every own s_i=r†_i({i})>0,
distinct nonempty reward entries within each recipient row, and

    0<δ=Δ_all(r†)<Δ_abs(r†)=δ+g, g>0.               (P1)

EVERY full-carrier minimum pair has ONE common debt vector d*.
Every sufficiently near-minimal ACTUAL independent profile has
joint Never mass, each individual Never mass and EVERY debt
bounded below by positive constants depending on this table.
In particular no full minimum belongs to K_abs.

For ANY finite-law minimizing sequence at this fixed table and
ANY subsequence with the marked convergences proved in Section6,
EVERY resulting marked full minimum q satisfies:

1. All four prescribed Never masses are positive and all four
   debts are positive. Literal Never is STRICTLY below the full
   response cap for EVERY owner.
2. No prescribed clock precedes the earliest complete maximizing
   response τ. This τ is finite, isolated, a positive MIXTURE
   atom, and the FIRST prescribed stage.
3. At least TWO owners have positive root atoms. EVERY positive
   root rate is strictly below1; there is NO sure root owner.
   The root continue product is positive, and its independent
   root outcome has at least three positive nonempty labels.
4. A PAID owner i maximizes at τ and at a LATER FINITE compact
   response σ. These two PAYOFF kernels differ on a set of
   positive original opponent probability, although their
   expectations equal B_i. Original moving FINITE responses
   witness the distinction and have positive gain eventually.

Moreover, with n_i=q_i(Never), ν=∏n_i, h_i=∏_(j≠i)n_j and
R_i=V_i(Never), the ORIGINAL finite blocks' honest periodic
repetitions have exact full-cap limit max(B_i,R_i/(1−h_i)).
Their absorbing-domain floor forces

    Σ_i[R_i/(1−h_i)−B_i]⁺
      ≥g+ν/(1−ν)·Σ_i U_i>g>0.                     (P2)

Thus plain block renewal is genuinely priced: some new conditional
Never cap rises strictly above its old full cap. No changed full
response branch is omitted.

This table is selected BEFORE every final minimum sequence.
No old law, cap selector, chronology, MAX source, minimizing tail
or Nash root is transported. The selection does NOT assert
additional finite raw contact exclusions or absorbing membership
of the final full minima. It makes those minima strictly
NONabsorptive instead. The result rules out zero-debt bridges
and sure first roots at one fresh counterexample table, not at
every original reward table.

It does not construct a paid return, compatible charge, Nash
continuation, finite-support minimum, raw-time-tight law limit or
uniform payoff. The counterexample hypothesis and all remaining
strategic quantifiers are retained; the full conjecture is open.

### 2. Original semantics and the checked counterexample normalization

The actual quitting game pays zero at the live date when the quitting
coalition is selected; its absorbing reward starts at subsequent
dates. Terminal rewards encode the asymptotic payoff, so this one-date
convention is not altered by the terminal calculations here.

On the unique live history at each date, each behavioral strategy has
a hazard sequence, equivalently an independent stopping law. A complete
unilateral behavioral replacement has the same terminal payoff as
replacement of that owner's whole stopping law. Since the replacement
payoff is affine in its law, its supremum is the supremum over pure
finite deadlines and Never. The exact tracked correspondences are

- `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`,
  `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`,
  `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff`, and
  `quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`
  in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.

The exact original no-UE bridge is
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`. Its
positive-gap assertion uses one positive gain against EVERY complete
behavioral profile, with an unrestricted unilateral deviation. Its UE
target is one payoff vector fixed before accuracy, with accuracy-dependent
profiles valid at all sufficiently long horizons.

Such a gap g>0 gives D_r(p)≥g for every actual law profile, hence
Δ(r)>0. Conversely, Δ(r)=d>0 implies some owner's debt is at least
d/4 at every profile. Approximate that owner's supremum by an actual
pure response within d/8. This gives an actual terminal gain at least
d/8 and therefore excludes a uniform-equilibrium payoff by the named
bridge. Natural-number caps need not attain their supremum.

For the initial normalization, first observe that some
s_m>0 in any counterexample: otherwise actual AllNever has U=B=0
and D=0, contrary to the positive-gap bridge.

The checked theorem
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`
takes an actual Fin4 no-UE game and gives its full recursively
stabilized normal core. Then
`all_punishmentNormal_of_normalCore_eq_univ` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean`
gives its actual all-player punishment normality P_i≤s_i.
Here P_i is the infimum, over independent opponent behavior profiles,
of the responding player's complete best-response value. No supplied
punishing strategy or attainment is required.

For the positive pivot m define

    h_m=0,  h_i=s_i for i≠m,
    r′_i(S)=(r_i(S)−h_i)/s_m.

The definitions `quittingSinglePivotOffset`,
`quittingSinglePivotNormalizedReward` and the own-singleton identity
`quittingSoloReward_singlePivotNormalized` are in
`UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean`.
The own vector of r′ is exactly e_m. The actual reverse transport
`isUniformEquilibriumPayoff_original_of_singlePivotNormalized` in
`UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean`
requires precisely s_m>0 and original ∀i P_i≤s_i. It takes any
fixed uniform payoff target of r′ to one of r. Thus r′ remains a
counterexample and has positive FULL gap. It is not an unchanged-law
or minimum-profile affine-invariance claim.


### 3. Signed row translations and the complete coupling estimate

For any actual profile let n_i=p_i(Never), ν=∏_i n_i and
h_i=∏_(j≠i)n_j. Against fixed independent opponents, bounded
convergence gives

    lim_(t→∞) V_i(t)=V_i(Never)+h_i s_i.             (P3)

When an opponent exits finitely, sufficiently late finite replies
are passive at its first coalition, just as Never. On the
all-opponent-Never cylinder, the late reply is the sole quitter
and pays s_i, while Never pays0. Therefore if s_i≥0, the FULL
cap equals the finite-response supremum.

Add C to EVERY nonempty coordinate of recipient row i, leaving
Never0. Assume BOTH s_i≥0 and s_i+C≥0. Every finite pure-response
payoff increases by exactly C. The finite supremum, hence full
cap, increases by C because the same finite-supremum fact holds
before and after. Prescribed delivery increases by C(1−ν).
Thus, for EVERY actual profile,

    B_i^new=B_i+C,
    U_i^new=U_i+C(1−ν),
    d_i^new=d_i+Cν.                                (P4)

Other recipients' coordinates are unchanged. C is allowed to be
NEGATIVE provided the new own singleton stays nonnegative.
This is not general affine invariance for signed own rewards.
On P_abs, ν=0, so its ENTIRE pair translates by(U_i,B_i)↦
(U_i+C,B_i+C). Closing gives the same affine map on K_abs and
preserves its total-debt minimum value.

Move ONLY owner i's old Never atom to finite deadline t. Its
prescribed payoff gain is n_i[V_i(t)−V_i(Never)] and is at most
its old complete debt. Taking t→∞ gives the exact bound

    ν s_i≤d_i.                                     (P5)

The tracked behavioral declaration is
`prod_stoppingLaw_none_mul_singleton_le_terminalDebt` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.
Its actual-profile statement has no cap-attainment or sign
hypothesis. Its use with s_i>0 here controls JOINT Never mass,
not every individual mass by itself.

There is also a uniform whole-pair absorbing completion estimate.
Choose an owner with the smallest Never mass e≤ν^(1/4), and
move its ENTIRE Never atom to ANY one finite date. The resulting
actual profile is in P_abs. Independent coupling changes every
prescribed payoff by at most2Me, where M>0 bounds the table.
For every respondent other than the changed owner, ALL finite
and Never response payoffs change by the same bound, uniformly.
The changed owner's cap is unchanged because its own law is
deleted by a response. Taking all full suprema gives total-debt
error≤(4+3)2Me=14Me. Consequently, for EVERY actual profile,

    Δ_abs(r)≤D_r(p)+14Mν(p)^(1/4).                  (P6)

This estimate is valid independently of a Nash or minimum premise.
If ν=0 it simply says the absorbing profile has debt at least
Δ_abs. It compares WHOLE full-cap pairs, not selected testers.

For two tables at sup distance e, every prescribed payoff and
EVERY pure-response payoff at the SAME laws changes by at most e.
Caps change by at most e. Taking infima over either fixed actual
class gives

    |Δ_all(r)−Δ_all(r′)|≤8e,
    |Δ_abs(r)−Δ_abs(r′)|≤8e.                        (P7)

No old minimizing profile is held fixed when these value moduli
are applied.

### 4. Small positive constants produce strict FULL/absorbing gap separation

The normalized actual counterexample r′ of Section2 has own
vector e_m and Δ_all(r′)>0, hence Δ_abs(r′)>0.
Subtract1 from EVERY nonempty coordinate in recipient row m,
leaving all other rows and Never0 unchanged. Its own reward
moves from1 to0, so(P4) applies with both own signs nonnegative.
Call the resulting table z. ALL four own singletons of z are0,
and its absorbing gap is

    Δ_abs(z)=Δ_abs(r′)=A>0.                         (P8)

Ordinary Δ_all(z)=0 at AllNever is expected and harmless. We
do not claim z itself is an ordinary no-UE game. The absorbing
gap, not its unrestricted gap, is retained.

Choose0<t<A/8 and add t to EVERY nonempty entry in EVERY row.
Call the table z^t. Its own vector is(t,t,t,t). Equation(P4)
gives, at EVERY actual independent law,

    D_(z^t)(p)=D_z(p)+4tν(p),
    Δ_abs(z^t)=A,
    Δ_all(z^t)≤D_(z^t)(AllNever)=4t<A/2.            (P9)

Its full gap is nevertheless POSITIVE. Since tν≤d_i≤D by(P5),
the absorbing completion bound(P6) at z^t gives

    A≤D+14Mν^(1/4)≤D+14M(D/t)^(1/4).

If D≥A/2 it has a positive lower bound. Otherwise this inequality
forces D≥t(A/(28M))⁴. Therefore

    Δ_all(z^t)≥min(A/2,t(A/(28M))⁴)>0.              (P10)

This is an all-profile proof. By the tracked original exploitability
gap correspondence z^t is an actual counterexample again.
SMALL constants deliberately put its original FULL minimum BELOW
the absorbing floor. No infinite-penalty limit, finite penalty
attainment or companion absorbing minimum is used.

### 5. One row-generic table and one common debt vector at ALL full minima

Scale z^t by a common positive reward bound into the unit cube,
and contract slightly inward. Both gap values scale by the SAME
factor. They remain positive and strictly separated; every own
reward stays positive. Every entry is strictly inside the cube.

By(P7), choose a small sup-norm perturbation ball preserving
Δ_abs>Δ_all>0 and all s_i>0. Avoid the finitely many hyperplanes
r_i(S)=r_i(S′) within each row. Their complement is dense.
Choose r̂ there. All within-row nonempty entries are distinct.
Write δ̂=Δ_all(r̂)>0 and ĝ=Δ_abs(r̂)−δ̂>0.

#### Fixed-carrier concave scalarization

Let K be the ORIGINAL compact payoff/cap carrier for r̂, and let

    A={a∈ℝ⁴:a_i=B_i−U_i for some (U,B)∈K}.

A is compact, nonempty and nonnegative; each coordinate is at most2
in the unit reward cube. These facts follow directly from the actual
carrier definition, compactness and nonnegative debt. On the positive
orthant define

    W(θ)=min_(a∈A) Σ_i θ_i a_i.

This is CONCAVE because it is an infimum of linear functions of θ.
It is finite and Lipschitz, with

    |W(θ)−W(η)|≤2Σ_i|θ_i−η_i|.

This does not convexify the set of stopping laws or the carrier. The
concavity comes from scalarizing one fixed attainable debt set, not
from a false Jensen rule for independent profile mixtures.

For the scaled reward r̂^θ_i(S)=θ_i r̂_i(S), the SAME actual laws have
U_i^θ=θ_i U_i, B_i^θ=θ_i B_i, and debt θ_i a_i. Supremum commutes
with multiplication because θ_i>0. The positive diagonal map is an
invertible continuous map on the eight semantic coordinates, so it
also carries K onto the ORIGINAL closed carrier K_θ for r̂^θ. Hence

    Δ_all(r̂^θ)=W(θ),
    min_i θ_i ·δ̂≤W(θ)≤max_i θ_i ·δ̂.              (DR1)

Here δ̂=Δ_all(r̂)>0. The lower bound uses nonnegative debts at ALL actual profiles and
extends to the closure. The upper bound evaluates an old true SUM
minimum. Therefore every positive θ retains a positive gap. Positive
row scaling is strategically equivalent for exact Nash and, after
rescaling accuracy, for uniform-payoff existence; it does not manufacture
a different deviation probability mode.

#### Real regular scales cover EVERY minimizing pair

For almost every θ in any open positive box, every coordinate partial
derivative ∂_i W(θ) exists two-sided. An elementary proof suffices:
for each fixed choice of the other three coordinates, the one-variable
function is finite concave, with monotone one-sided slopes and only
countably many points of unequal slopes. Fubini gives a null exceptional
set for that coordinate in the box; take the union for four coordinates.
The relevant one-sided slopes are measurable difference-quotient limits.
No joint differentiability or unproved unique-minimizer theorem is needed.

For ANY minimizing a∈A at such a θ,

    W(θ+t e_i)≤W(θ)+t a_i.

Divide by positive t and negative t separately and let t→0. Equality
of the two coordinate derivatives forces

    a_i=∂_i W(θ) for EVERY i and EVERY minimizing a.          (DR2)

Thus ALL old-carrier θ-minimizers have one debt vector ∇_coord W(θ),
and ALL scaled-table SUM minimizers have the ONE common vector

    d*_i=θ_i ∂_i W(θ).                            (DR3)

There may still be multiple minimizing laws, calendars, prescribed
payoffs, caps, active tests and cap dates. The result is DEBT rigidity,
not pair rigidity. Equation (DR2) uses an objective LINEAR in θ on one
FIXED compact carrier. Its complete minimum-family conclusion follows from the
two supporting inequalities, not a selected profile derivative.


Choose the coordinate-regular θ in a sufficiently small positive
box close to1, inside(1−ρ,1)⁴. Such choices exist by the proved
null exceptional-set assertion. The scaled table r† is still
unit-bounded with all own rewards positive and rows distinct.
Because its sup distance from r̂ is at mostρ, choose8ρ<δ̂
and16ρ<ĝ. Equation(P7) then preserves

    δ=Δ_all(r†)>0,  g=Δ_abs(r†)−δ>0.

Every full minimum of THIS fixed final table has the ONE vector
d* proved above. The old table's weighted minima have been mapped
to the CURRENT table's genuine UNWEIGHTED SUM minima. Nothing
about an old minimizing law or an old active test was assumed.
All subsequent sources use this final table and its true full
minimum, with M=1 permissible.

### 6. Actual finite sequences produce the marked global source

Fix a positive finite reward bound M and δ=Δ(r)>0. The ORIGINAL
closed attainable payoff/cap carrier is nonempty and contained in
[−M,M]⁸, hence compact. Every actual debt coordinate is nonnegative
because the prescribed own law is an admissible response; this
extends to the closure. Continuous total debt attains its minimum
there, and that minimum equals the infimum over actual pairs.

First, finite-support
stopping laws have the SAME infimum. Move each owner's finite mass
after K to Never, writing a_i(K) for the moved mass. Independent
coupling changes prescribed outcomes only if a changed draw occurs,
so every prescribed payoff changes by at most 2MΣ_j a_j(K). For
ANY response of i, the same bound uses only opponent changes, uniformly
over all finite responses and Never. Taking suprema gives complete-cap
convergence. Since a_i(K)→0, D converges and the infima agree.
Choose finite profiles p^k with D_r(p^k)→δ. To realize any selected
full minimum pair, first choose actual pair approximants to that pair
and then finite-approximate each of them with vanishing coupling error.
The same construction below applies to EVERY such minimizing sequence.

Put μ^k=Σ_i p_i^k/4. In chronological order partition [0,1] into
intervals whose lengths are the positive masses of μ^k, with Never
last. For a date a on its interval define

    f_i^k(u)=p_i^k({a})/μ^k({a}).

These are deterministic charts, NOT a common random signal. Coordinates
are still independently sampled. They satisfy 0≤f_i^k≤4,
Σ_i f_i^k=4 a.e., and ∫f_i^k=1. Separability of L¹ and bounded
weak-* compactness give a common subsequence f_i^k⇀*f_i. Let
c_k=1−μ^k({Never})→c. Let E_k contain all interval endpoints,
including 0,c_k,1. Locate every actual finite pure response t at

    x_k(t)=μ^k({a:a<t})+μ^k({t})/2.

A supported date is its interval midpoint; an empty date is a cut;
all finite dates after the last finite support have location c_k.
The resulting finite sets T_k have a Hausdorff limit T. Pass also
to E_k→E. Then T⊆[0,c] is nonempty compact, c∈T, and
0,c,1∈E. Never is a separate isolated final label, not c.

Every component J=(a,b) of [0,c]∖E comes from ONE original atom
interval J_k=(a_k,b_k)→J: a compact subinterval of J eventually
contains no endpoint, so lies in one atom, whose endpoints must
converge to a,b. Thus T∩J consists of its midpoint. Each f_i is
constant a.e. on J, by testing two interior subintervals and taking
weak-* limits of the same original constants. The same argument gives
constancy on (c,1), when that Never interval is nonempty.

The set (E∩[0,c])∖T is null. Indeed every component of [0,1]∖T
has at most one E point: two separated limiting endpoints would force
an original atom midpoint between approximating endpoints, contrary
to that component's separation from T. There are only countably many
components. Collapse every J to its midpoint, keep the remaining
E∩[0,c] points, and send (c,1) to Never. This defines a map π a.e.
Set q_i=π_*(f_i du), with X=T⊔{Never}. Its average law is π_*du.

Every positive finite mixture atom is a retained component midpoint,
ISOLATED in T by half its interval length. Every other finite point
has zero mixture and own mass. In particular q_i({c})=0. Never is
isolated regardless of its mass. These are facts of the producer,
not assumptions on arbitrary abstract compact laws.

Products ∏_i f_i^k converge weak-* to ∏_i f_i: this holds first on
rectangle tests by marginal weak-* convergence, then on every L¹
test by density and the common bound 4⁴. Likewise for opponent
products. Let K_S^k be the prescribed first-coalition indicators on
the OLD chart, and K_S the limiting indicators. They converge a.e.
and in L¹. Exclude the countably many retained endpoints, c, and
equal independent raw Lebesgue coordinates. Two remaining coordinates
either lie in one retained interval, hence eventually tie in its
original interval, or have a limiting endpoint strictly between them,
hence eventually lie in ordered different atoms. Never membership
also stabilizes. For any such kernel use

    ∫K_S^k R^k−∫K_S R
      =∫(K_S^k−K_S)R^k+∫K_S(R^k−R).

The first term is bounded by 4⁴ times the L¹ kernel error, the second
is a FIXED-kernel weak-* test. Hence prescribed outcomes and payoffs
converge, without multiplying two uncontrolled weak limits.

For ANY moving finite response with x_k→x∈T, a retained midpoint
forces the original corresponding midpoint eventually; its exact tie
is preserved. At every other x there is zero mixture atom, so all
opponent comparison kernels converge a.e. and in L¹. The same split
proves response-payoff convergence. This includes x=c, the last finite
response, DISTINCT from Never; Never's separate kernel also converges.
The limiting V_i is continuous on T: isolation handles midpoints,
zero-atom cut continuity handles the remaining points. It is continuous
on X since Never is isolated.

The limiting laws retain the independent product first-coalition
rule. Bounded Fubini therefore also gives

    U_i(q)=∫_X V_i(t,q_-i) dq_i(t).

Thus debt is the expectation of a nonnegative pure-response regret
integrand. This identity also applies to the legal old-law families
below; zero expected regret restricts their prescribed support to
the complete maximizing set.

Extract original maximizing tests for the cap upper limit, and
approximate a limiting maximizing point by T_k for the lower limit;
retain Never separately. Compactness and continuity give

    U_i(p^k)→U_i(q), B_i(p^k)→B_i^X(q), D_X(q)=δ.       (1)

The pair (U(q),B^X(q)) belongs to the ORIGINAL closed attainable
payoff/cap carrier. That carrier is defined by
`quittingTerminalSemanticCarrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` as the
closure of actual behavioral pairs. Equation (1) proves membership,
and continuity of total debt gives global minimum δ over that carrier.
The same conclusion holds for EVERY subsequence satisfying these
convergences from ANY chosen finite-law minimizing sequence.

An extra formal finite tester c⁺ after c has the SAME response payoff
as c whenever the modified laws have zero mass at c: all finite
opponent exits are earlier; against all-opponent-Never the responder
is the sole quitter. We retain this duplicate explicitly in arguments
below but do not identify either finite test with Never. Uniqueness
always counts points of X, not this duplicate representation.

### 7. Signed old-law variations and complete cap stability

Only two kinds of affine target law are needed:

    (a) an EXISTING positive own atom δ_t;
    (b) an OLD conditional law q_i(·|clock in A), q_i(A)=e>0,
        where A is a strict early or late ordered cut.

For each owner independently use q_i^λ=(1−λ_i)q_i+λ_iν_i.
For (a), with m=q_i(t)>0, the target mass is m+λ_i(1−m),
and all other masses have factor 1−λ_i; a two-sided interval about
zero is legal. A unit-mass atom has a redundant direction. For (b)
the likelihood factors on A and its complement are respectively
1+λ_i(1/e−1) and 1−λ_i. A sufficiently small two-sided interval
makes both positive; e=1 gives a redundant direction. No negative
probability or new stopping clock is introduced.

For (a), the original retained interval J_k→J has positive length,
including the Never interval when the target is Never. Its own mass
m_i^k→m>0. The original finite law

    p_i^{k,λ}=(1−λ_i)p_i^k+λ_iδ_(t_i^k)

is legal on a common small signed interval and has OLD-chart density

    (1−λ_i)f_i^k+λ_i 1_(J_k)/|J_k|.

Normalized interval indicators converge in L¹; the densities remain
bounded and converge weak-* to the desired limit.

For (b), use the corresponding original conditional finite law.
At a retained atom, strict-before means the LEFT interval endpoint,
strict-after means the RIGHT endpoint, including Never on the late
side. At Never the early cut is c_k. At a zero-mixture-mass cut, take
old endpoint cuts converging to its raw-chart boundary; there is no
positive limiting mass at that boundary. Such cuts exist by E_k→E:
each boundary of an initial segment for the monotone collapse π is
in E. They correspond to a union of whole original atom intervals,
so are legal chronological conditionals on the unchanged calendar.
The cut indicators converge strongly in L¹ and e_i^k→e>0. The new
density is exactly

    f_i^k[(1−λ_i)+(λ_i/e_i^k)1_(A_k)].               (2)

Strong cut-indicator convergence removes the moving-cut error against
any L¹ test, using the common density bound; the remaining fixed
multiplier uses weak-* convergence. Thus these new densities remain
bounded, legal and weak-* convergent on the OLD chart.

All old collapse maps, test sets, prescribed kernels and moving-test
kernels are unchanged. The Section 6 product and kernel argument
therefore proves BOTH prescribed-payoff and full-cap convergence for
every fixed vector of signed parameters. Every sequence of original
maximizing finite tests has an old-chart subsequential limit; fixed
limiting tests give the reverse bound. Never and c are separate,
and c⁺ duplicates c since all these targets retain zero mass at c.
Consequently

    D_X(q^λ)=lim_k D_r(p^{k,λ})≥δ.                    (3)

Every modified pair is in the original semantic carrier. Equation (3)
is a whole-actual-law floor, not a verifier on an abstract target
family. The argument also realizes a nonsigned conditional target
at λ=1 when its positive mass is fixed. Far polynomial evaluations
below, however, do not assert full-cap stability at that endpoint.

#### Whole active-family stability and the multiaffine minimum principle

If a unique maximizing point τ is isolated, continuity on compact X
gives a UNIFORM gap on X∖{τ}. Product coupling gives, uniformly over
ALL tests, payoff changes at most 2M times the sum of opponents'
total-variation changes. Thus isolated unique caps remain at their
old points on a sufficiently small legal signed box.

A nonisolated unique cap does NOT supply such a complement gap. The
following exact identity is used instead. Suppose target changes can
be expanded in each opponent coordinate as a positive multiple of
the original law plus a signed early submeasure, whose support is
before a common cut a. Every product term containing an early
submeasure has a finite exit before ANY response t>a, including
Never. Its payoff is independent of t. Hence

    V_i(t,q_-i^λ)=k_i(λ)V_i(t,q_-i)+C_i(λ),
    t>a, k_i(λ)>0,                                 (4)

where C_i is independent of t. A compact lower set excluding the
old cap has a strict uniform gap, preserved by total-variation
control. Formula (4) preserves ordering among ALL upper tests, so
the nonisolated cap stays fixed without an assumed uniform gap there.

In particular a late conditional ν=q(·|clock>t₀), e>0, satisfies

    q^λ=[1+λ(1/e−1)]q−(λ/e)q|_(clock≤t₀),          (5)

where the final term is an EARLY unnormalized submeasure. A supported
reset δ_t with t≤h is also an early replacement. Choose h<a below
all late displayed caps; if all those caps are Never choose h<a<c.
A positive finite atom is strictly before c, so the latter cut exists.
These formulas remain valid for signed parameters and every response
above the cut, not merely the displayed maximizers.

When all four caps remain at τ_i on an open signed box, define

    F(λ)=Σ_i[V_i(τ_i,q_-i^λ)−U_i(q^λ)].             (6)

Each independent law is affine in its parameter, so F is multiaffine.
On this box F=D_X≥δ=F(0) by (3). A multiaffine polynomial with an
interior minimum is algebraically constant. Indeed its average over
every centered sign cube is F(0); if its first nonzero squarefree
homogeneous part existed it would have a negative sign direction,
contradicting the local minimum for small scaling. Redundant directions
do not change this conclusion.

Thus F≡δ as a polynomial. The all-one value can be evaluated
ALGEBRAICALLY even when the distant endpoint does not preserve old
caps. We NEVER infer that this endpoint is Nash, has actual debt δ,
or is a minimizing tail. Only the small signed box has fixed caps.


### 8. The checked strict margin at a true original unweighted Fin4 minimum

Write s_i=r_i({i}). The exact tracked input is
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`,
under its actual imports. Its hypotheses are: a pair in the ORIGINAL
closed attainable carrier; unweighted total debt no larger than
that of EVERY pair in this carrier; exactly four players; M>0;
|r_i(S)|≤M for every finite coalition and recipient; and δ>0.

At such a pair, with d_i=B_i−U_i and Σ_i d_i=δ, it concludes

    B_i−s_i≥δ+δ²/(8M),
    U_i−s_i≥δ−d_i+δ²/(8M)>0 for every i.             (QM)

The final strict inequality uses 0≤d_i≤δ, already true throughout
the original closed carrier. This is a theorem about the TRUE
unweighted SUM minimum, not a restricted strategy minimum, weighted
minimum at an old table, selected cap, Nash tail or original first-row
Nash condition. Every invocation below occurs at a produced global
minimum of the currently fixed table. For unit-cube tables use M=1.
No singleton sign or same-table punishment premise is needed.

### 9. A uniform actual Never floor and positive debt at EVERY full minimum

For ANY actual p at this final table, moving the smallest Never
atom as in Section3 gives

    δ+g≤D(p)+14Mν(p)^(1/4).                       (P11)

Hence EVERY sufficiently near-minimum profile, for example
D(p)≤δ+g/2, satisfies

    ν(p)≥(g/(28M))⁴=:η_near>0,
    p_i(Never)≥η_near,
    d_i(p)≥s_iη_near>0 for EVERY i.                (P12)

For any original full-minimum pair and ANY actual realizing
sequence, all subsequential Never-mass limits instead satisfy

    ν≥(g/(14M))⁴=:η>0.                            (P13)

The marked compiler retains these marginal Never masses: its
Never interval has the limiting total mass, and strong moving-
interval/weak-* density convergence gives each own mass. Thus
every produced marked minimum has all n_i=q_i(Never)≥η and
all d_i≥s_iη. This also follows by taking limits in the exact
joint-Never debt bound. The common vector d* is therefore
STRICTLY positive in every coordinate.

For every actual and marked response menu,

    B_i≥V_i(Never)+h_i s_i,
    h_i=∏_(j≠i)n_j≥ν≥η at a minimum.               (P14)

The last finite compact tester is the limit of delayed finite
responses and is DISTINCT from literal Never. Thus Never is
STRICTLY suboptimal for every owner. All full maximizing points
lie in the FINITE compact test set. No raw-ℕ cap attainment is
inferred; a maximizing finite compact endpoint can still require
moving original deadlines.


#### First prescribed collision: no earlier mass and no sure supplier

Use the actual marked source of Section6 and the legal signed
chronological conditionals and complete active-family stability
of Section7. They apply to ANY finite-law full-minimum sequence;
no finite contact-separation condition is required.
The point q is in the ORIGINAL full carrier at δ and has d*.
Never is isolated and nonmaximizing by(P14). Let τ be the
earliest FULL maximizing point among all owners.

For any regular ordered cut u<a<τ with a positive head, put
B={i:e_i=q_i(clock≤u)>0}. For each i∈B vary BOTH signs toward
its OLD head conditional. Because n_i≥η, EVERY e_i<1. The
original whole-date/raw-boundary transport realizes all these
families in the full carrier. All upper response kernels have
the SAME positive affine transformation; the compact lower
tester set has no old maximum and keeps a strict uniform gap.
Thus FULL active families stay fixed on a small signed box.

The summed-regret multiaffine polynomial has an interior true
minimum δ and is constant by Section7. Every pair on the small
cap-stable box is therefore a full minimum. Section5 makes EACH
regret polynomial equal to d*_i on that open box, hence
identically d*_i as a polynomial. Far polynomial evaluations
need not represent true endpoint debts.

If B={h}, conditioning only h to its head gives own payoff s_h
(all opponents are later), hence original U_h=s_h. Indeed its
own cap is independent of its own law, and the individual debt
polynomial is constant, so its prescribed-payoff polynomial is
constant too.
This contradicts the tracked strict quadratic prescribed margin
at a positive FULL Fin4 SUM minimum.

If |B|≥2, fix i∈B and condition all other B owners to their
heads in the polynomial. Its own late branch and its selected
response≥τ are both screened by a sure other head, so the late
regret is0. The all-head selected regret is d*_i, giving

    d*_i=e_i d*_i.

Since d*_i>0 and e_i<1, this is impossible. Far endpoint caps
are not claimed fixed: only polynomial constancy is evaluated.
There is therefore NO positive prescribed mass before τ.

If the mixture had zero atom at τ, every opponent would stop
strictly later and an owner active at τ would get exactly s_i,
contrary to the full cap-minus-singleton margin. So τ is a
positive mixture atom, isolated by the retained chart, and the
FIRST prescribed stage. Its own rates a_i=q_i({τ}) satisfy

    a_i≤1−n_i≤1−η<1,
    ∏_i(1−a_i)≥ν≥η.                               (P15)

There cannot be just one supplier h with 0<a_h<1. The literal
original conditioned suffix after the retained root belongs to
the same full carrier and has total debt≥δ. On the original sequence,
condition all owners on surviving that full root date, delete the
prefix and rebase the suffix. Its positive continue product stays
bounded away from0 by(P15). The Section6 kernel argument then
puts its entire limiting pair in K_all, not just its selected
responses. For that suffix write its payoffs and full caps as U_i′,B_i′.
For i≠h the original prescribed payoff is
U_i=a_h r_i({h})+(1−a_h)U_i′, while responses strictly after
the root give B_i≥a_h r_i({h})+(1−a_h)B_i′. For h, its
opponents have no root atom, so B_h=max(s_h,B_h′). The strict
bound in Section8 makes B_h>s_h, hence B_h=B_h′, and
U_h=a_h s_h+(1−a_h)U_h′. Thus d_h=(1−a_h)d_h′+
a_h(B_h−s_h), while d_i≥(1−a_h)d_i′ for every i≠h.
The exact total ledger is therefore

    δ≥(1−a_h)D_tail+a_h(B_h−s_h)
      ≥(1−a_h)δ+a_h[δ+δ²/(8M)]>δ.

This is impossible. It is the all-tail floor, NOT tail optimality
or Nash. At least TWO suppliers are therefore STRICTLY mixed.
Independence makes the root's singleton labels for either supplier
and their pair label all positive (set all other root draws to
Continue, an event of positive probability). Prescribed Never
also has positive probability. No deterministic-outcome spectrum
or literal coalition release is needed to exclude this geometry.


### 10. A PAID first-to-later FINITE payoff-kernel bridge

Suppose no owner maximizes at both τ and a later point. Every
cap containing τ is then root-only; other complete cap families
lie strictly later. Independently reset the EXISTING positive
root atoms toward τ with small parameters of BOTH signs.
Root-only caps have isolated complement gaps. On whole later
families all response kernels change by one positive affine
map, since a term containing a reset opponent exits at τ.
A compact lower gap remains strict. Thus the entire root box
is cap-stable, with legal original signed transport, including
all moving tests and literal Never.

The summed polynomial is constant by globality, and EACH polynomial
is constant by common debt. A root supplier whose cap is root-only
has d_h(λ_h)=(1−λ_h)d*_h; rigidity contradicts d*_h>0.
If its caps are later, set every other root supplier algebraically
to τ. There is another sure root owner. Its old late branch
and selected response are screened identically, giving

    d*_h=a_h d*_h.

This contradicts d*_h>0 and a_h<1. Hence a root/later bridge
exists. Its later point σ is FINITE, since(P14) excludes Never
from EVERY active set. The owner has positive debt, uniformly
bounded below by s_iη, and a pure first-root response on the
original sequence has terminal gain≥d*_i/2 for all large indices.

The first response value B_i>s_i implies a positive opponent-
root event. On any nonempty tied opponent set S at τ, response
τ pays r_i(S+i), whereas response σ>τ pays r_i(S). At least
one such S has positive probability; row genericity makes its
reward difference nonzero. Both expected values equal B_i.
Section6 supplies original retained root dates n_k and moving
FINITE responses t_k whose chart locations tend to σ. Isolation
of τ and σ>τ force t_k>n_k eventually. The probability that
precisely the nonempty opponent set S ties at n_k tends to its
positive marked probability. On that original event the two
responses pay the literal row entries r_i(S+i) and r_i(S).
This gives exact positive-event kernel distinctions for large indices,
and their values tend to B_i. Exact co-maximality at each raw
finite index is NOT asserted.

This is a source-level strict increment: the bridge is PAID,
finite-to-finite, and has NO sure root owner. It does NOT give
admissible return, paid renewal, compatible charge or UE. All
four complete debts can still leak to nonmovers after a reset.


### 11. An actual whole-block periodic competitor prices the residual

Write R_i=V_i(Never), ν=∏n_i and h_i=∏_(j≠i)n_j at ANY
produced marked full minimum. Section9 supplies at least two finite
root suppliers, so h_i<1 for EVERY i, and ν<1. The strict
quadratic full-minimum margin gives U_i>s_i>0 and B_i>s_i.

On an original finite-law approximant, let N be its last supported
finite date and choose length L=N+2. This includes the EMPTY
final phase N+1, strictly after every finite prescribed draw. Repeat its hazard block
PERIODICALLY forever on the live history. Each owner redraws
only its own private independent law each new block. The honest
periodic profile absorbs almost surely because ν<1. Some owners
may still prescribe Never forever if their n_i=1; full absorbing
play, not all-four-finite play, is sufficient here.

The one-block prescribed reward is U_i and joint block survival
is ν, so repeated delivery is U_i/(1−ν). A responder can wait
k complete blocks and then use any one-block finite test t.
Its payoff is

    R_i(1+h_i+…+h_i^(k−1))+h_i^k V_i(t).

Literal Never in the periodic opponents gives R_i/(1−h_i).
The old finite support menu contains its full finite supremum
(include one empty final date), and own positivity makes that
supremum the OLD full cap. Taking the supremum over ALL k,t
and Never therefore gives the EXACT unrestricted periodic cap

    B_i^rep=max(B_i,R_i/(1−h_i)).                  (P16)

Every unrestricted behavioral response is covered: its payoff is
affine in its complete stopping law, hence is bounded by these
pure finite deadlines and Never. This is not merely a within-
one-cycle comparison or a finite word ending in Never.

The generic signed interpolation and unrestricted cap upper bound
are already tracked in
`UniformEquilibrium/Quitting/Cycles/PeriodicFiniteReplyPrefix.lean`:
`quittingPureTimeValue_periodizedPrefix_block_interpolation`
and `quittingPeriodicWindowRefusalValue_periodizedPrefix_eq_div`
assume the responding owner's opponent prefix survival is<1;
`quittingBestReplyValue_periodizedPrefix_le_max` additionally
assumes the chosen finiteBound bounds EVERY first-block finite
phase. That theorem covers unrestricted behavioral deviations
via `sSup_range_quittingTerminalPayoff_update_eq_periodicWindow`.
Here h_i<1 supplies its contraction hypothesis. The EMPTY final
phase and s_i≥0 make the finiteBound equal the OLD full cap.
A first-block maximizing phase and literal Never give the two
matching lower bounds, proving equality(P16), not only the
tracked upper bound. No new generic renewal formula is claimed.

The original finite approximants' U,B,R,n all converge to the
displayed marked data. The denominators stay bounded away from0
because the limiting root has at least two suppliers. Their
actual periodic profiles lie in P_abs and have debt≥δ+g.
Pass to the exact limit using(P16) to obtain

    Σ_i[R_i/(1−h_i)−B_i]⁺
      ≥g+ν/(1−ν)·Σ_i U_i>g>0.                    (P17)

This is a consumed all-law minimum comparison. In particular
some owner satisfies R_i>(1−h_i)B_i>0: its conditional passive
Never payoff creates a new upper cap upon full block renewal.
If every renewal cap stayed≤the old cap, periodic replay would
STRICTLY LOWER full debt, contradicting the original minimum.
This quantitative leakage is not a sign chosen at one old cap.


### 12. Complete exact boundary tables

These are solved games or hypothesis falsifiers, NOT examples
with a positive unrestricted gap. They test the steps of the
producer without weakening its counterexample premises.

#### Both singleton signs are essential in signed translation

Let r_i(S)=−1 for every i and nonempty S. At actual AllNever,
U_i=0 and B_i=0: finite responses pay−1 and Never pays0.
Adding1 to each whole row gives the identically-zero table,
whose AllNever payoff and cap are still0. Thus the cap does
NOT rise by1, and the debt identity(P4) fails if its OLD
singleton-nonnegative hypothesis is removed. It is not enough
that only the NEW own singleton is nonnegative.

#### Small constants cannot manufacture a positive absorbing gap

Here is a complete sixty-entry table by an explicit formula.
Put C={0,1,2}, with successor j+1 modulo3. For each nonempty
S⊆I set T=S∩C. The dummy recipient3 always gets0. For a core
recipient i:

- if T is empty or a singleton, set z_i(S)=0;
- if T={j,j+1}, give j payoff−1, j+1 payoff+1, and the
  remaining core recipient payoff0;
- if T=C, give every core recipient payoff−1.

This specifies every entry, including coalitions containing
the dummy, and every own singleton is0.

Give ALL four clocks independent geometric stopping hazards
q∈(0,1). They are all finite almost surely. Let
a=1−(1−q)⁴. Pair contributions cancel for every core recipient,
and core-triple contributions give

    U_i=−q³/a for i∈C, U_3=0.

For core i, a pure finite response at t has value
−q²(1−q)^(3t): the two single-opponent joining contributions
cancel; tying both core opponents gives−1; dummy exits
contribute0. Literal Never pays0. Hence EVERY core full cap
is0, the dummy cap is0, and

    D=3q³/[1−(1−q)⁴]→0.

Therefore Δ_abs(z)=0. Adding a common t>0 to all finite rows
preserves this absorbing-profile debt by(P4), although actual
AllNever now has total debt4t. Positive debt at one profile is
not a positive full gap. This is why(P8)'s A>0, produced from
an actual counterexample, cannot be omitted.

#### Honest block renewal can create a larger full cap

Let every own singleton be1, every passive coordinate be2,
and every participant coordinate of a nonsingleton coalition
be0. This formula specifies all sixty finite rewards.
Give every owner probability1/2 at date0 and1/2 at Never.
Exact independent enumeration gives, for every i,

    U_i=15/16, B_i=15/8, R_i=7/4,
    n_i=1/2, h_i=1/8, ν=1/16, D=15/4.

The root pure response pays1/8. EVERY later finite response
pays15/8; literal Never pays7/4. Repeat the two-date block
(root followed by its EMPTY final phase) periodically forever.
Then U_i^rep=1, but Never against the repeating opponents pays

    R_i/(1−h_i)=2>15/8.

The complete repeated cap is2 and D^rep=4. Formula(P16)
therefore cannot be replaced by B_i^rep=B_i. The cap birth
sum is1/2, prescribed amplification is1/4, and total debt
increases by1/4. All pure deadlines and Never are included.
The table itself has an exact terminal Nash profile: one
owner quits at date0 and all others prescribe Never; the
owner gets1 and every outsider gets2. Its full gap is0.

#### The empty final finite phase is essential

Let own singletons be1, passive coordinates0, and every
participant coordinate of a nonsingleton be−1. Again this
is a complete sixty-entry table. At the same half-root,
half-Never laws, the root pure reply pays−3/4, every later
finite reply pays1/8, and Never pays0. The old full cap is1/8.

If one repeats ONLY the root phase with period1, a finite
response at t pays−(3/4)(1/8)^t and Never pays0. Its repeated
full cap is0, so replacing the first-block phase supremum
by the OLD cap would be false. For the specified length2
block including the EMPTY final phase, response at phase1
pays1/8 and the repeated full cap is1/8, exactly(P16).
This chronology is why Section11 uses length N+2, not the
last supported date alone. The table is solved by a pure
singleton profile; this is a menu-completeness countertest.

### 13. Source scope, tracked overlap and the remaining consumer

The counterexample producer uses the tracked original
exploitability-gap correspondence, actual single-pivot reverse
transport, and normal-core punishment normality under their
stated hypotheses. It does not assume a normal core, actual
punisher, companion absorbing minimum or positive-own source
as an unproduced premise. Sections3–5 produce a fresh positive
FULL/absorbing separation, strict positive own rewards, and
common debt at EVERY original full minimum. Sections6–7
produce the actual marked full-carrier source and signed
variations from its original finite sequences. Section8's
quadratic margin is invoked only at a TRUE original minimum.

The generic periodic response interpolation and full-cap upper
bound are already implemented in the tracked declarations of
Section11. The additional conclusion is the whole-game producer
and the forced new-cap leakage(P17) at its separated minima,
not a newly claimed periodic best-response formula. No global
census of all earlier equilibrium classes is asserted.

This result is compatible with a counterexample. It narrows
the source at ONE new table: all four debts and all four
Never atoms are positive, the root has no sure owner, and
the first-to-later bridge is paid and finite-to-finite.
It does not preserve additional finite coalition-contact
exclusions or impose any old table's minimum debt vector.
Marked finite endpoints and literal Never remain distinct;
raw-integer full-cap attainment is never inferred.

The remaining complete-consumer problem is to exploit the
paid root/later tie together with its strictly priced
conditional-Never renewal cap to build ONE actual lower-debt
whole law, or derive an impossibility of this full active
family. A replay that omits its new Never cap is invalid.
No tail Nash, minimum tail, stagewise compatibility, charged
return or uniform-equilibrium producer follows from the
source restriction alone.


## Part II: an actual minimum-fibre operation and least-Never selection

### 14. The exact end wall and a genuinely old finite branch

Fix the ONE table produced in Part I. For a produced full minimum q,
write n_i=q_i(Never)>0, ν=∏_i n_i, h_i=∏_(j≠i)n_j, and
R_i=V_i(Never). The final EMPTY finite clock c has value

    V_i(c)=R_i+h_i s_i,

so κ_i=(B_i−R_i)/h_i≥s_i. The finite point c is not literal Never.
Let E_c={i:κ_i=s_i}.

First prove the exact common-source graft used below. For a finite
original approximant p^k, let L_k be its last finite support date.
Replace each owner's ORIGINAL Never branch by an arbitrary independent
finite tail w, starting at L_k+2. All original finite draws stay put.
There is no stretch between occupied dates: L_k+1 is an honest EMPTY
date retaining the old late-finite response price.

Every finite reply through L_k is unchanged. Every empty reply before
the new tail pays R_i^k+h_i^k s_i≤B_i^k. Every subsequent finite reply,
and literal Never, has value R_i^k+h_i^k V_i(t,w_-i), where V_i(t,w_-i)
is the corresponding complete tail-response payoff.
A nonempty original opponent exit screens the tail. On the original
all-opponent-Never cylinder, the arbitrary tail response is unrestricted.
Positive s_i makes old late-finite tests dominate old Never. Hence the
ENTIRE exact finite-index ledger is

    U_i(graft)=U_i^k+ν_k u_i(w),
    B_i(graft)=max(B_i^k,R_i^k+h_i^k b_i(w)).       (Q1)

Passing through the original marked convergence of U,B,R,n yields the
same formula at q. Actual finite tail approximants extend it to any
tail pair in K_all. If the tails absorb, the grafts absorb too, so
their limits belong to K_abs. Every born finite test and Never is
included; this is not a prescribed response selector.

#### 14.1. Some c-wall is active

The table's positive full floor excludes a uniform payoff. The exact
tracked source

    exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff

in UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean,
under its imports, provides a simplex λ with (Γλ)_i>0 for EVERY i.
Here quittingProjectiveLCPMatrix in
UniformEquilibrium/Quitting/Projective/SingletonLCP.lean defines
Γ_ij=r_i({j})−s_i, with recipient ROW i, and Γ_ii=0.

Use the actual one-date tail where player j quits with probability
ρλ_j and otherwise uses Never. For small positive ρ,

    u_i=ρ[s_i+(Γλ)_i]+O(Mρ²)>0,
    |b_i−s_i|≤2Mρ.

The full-cap bound follows from coupling every opponent law to Never:
the probability of any opponent finite draw is at most ρ, uniformly
over EVERY pure finite response and Never. Against all-Never opponents
the cap is s_i>0. The payoff expansion counts singleton-first events;
nonsingleton and singleton probability corrections are O(ρ²).

If every κ_i>s_i, fix sufficiently small ρ so b_i<κ_i for every i.
Formula(Q1) keeps EVERY original full cap fixed and increases EVERY
prescribed payoff by νu_i>0. For large original finite indices this
gives actual profiles with D<δ, contradicting the true ALL-law floor.
Thus E_c is nonempty at EVERY produced positive-Never minimum.

#### 14.2. Thin independent words control ALL clocks without pair spikes

For ANY simplex λ and ρ∈(0,1), use the actual finite laws

    p_j^N(k)=ρλ_j/N,  k=1,…,N,
    p_j^N(Never)=1−ρλ_j.

Date0 and dateN+1 are empty. Define

    μ_j=∫₀¹ ρλ_j ∏_(ℓ≠j)(1−ρλ_ℓ t) dt,
    u_i=Σ_j μ_j r_i({j}),
    F_i(θ)=s_i+∫₀^θ Σ_(j≠i) ρλ_j
                    ∏_(ℓ≠i,j)(1−ρλ_ℓ t) Γ_ij dt,
    b_i=max_(0≤θ≤1) F_i(θ).                       (Q2)

These are the limits of the actual FULL payoff/cap coordinates.
Prescribed pair ties have total probability at most6/N. On the no-tie
event, singleton-first probabilities are Riemann sums for μ_j, giving
the payoff limit. For ANY finite tester k, let
θ_N=clamp((k−1)/N,0,1). Earlier opponent first exits give the passive
singleton integral; if all opponents survive the test, its solo reward
is s_i. A collision at the TESTER's date has probability at mostρ/N;
ties among earlier opponents have probability O(1/N). All bounded
reward errors are therefore O(M/N), uniformly over ALL k, including
moving deadlines, date0 and arbitrarily late dates.

Every θ is approached by such finite tests; the late finite test
after the word represents θ=1. Literal Never has its separate passive
integral, and late finite adds s_i∏_(j≠i)(1−ρλ_j)>0 to it. Never is
therefore dominated by an actual finite response, not omitted. Thus
the finite supremum converges to max F_i, and affinity in the owner's
entire deviation law identifies it with the unrestricted behavioral cap.

Uniformly in θ, writing γ_i=(Γλ)_i,

    F_i(θ)=s_i+ρθγ_i+O(Mρ²),
    u_i=ρ(s_i+γ_i)+O(Mρ²),
    b_i=s_i+ργ_i⁺+O(Mρ²).                         (Q3)

The survival factors give these expansions directly. The finite word
rather than one common date is essential: it suppresses the first-order
pair-joining spike of a deviating deadline while keeping all clocks.

#### 14.3. The active c-wall cannot consist entirely of pure-Never owners

Apply(Q1) and the true all-law floor to the actual word(Q2), then
take N large. Dividing its debt change by ν gives, for every ρ,λ,

    Σ_i(b_i−κ_i)⁺/n_i ≥ Σ_i u_i.                 (Q4)

For i∉E_c the clipped term is zero for small ρ. Divide byρ and use(Q3):

    Σ_(i∈E_c)(Γλ)_i⁺/n_i ≥ Σ_i[s_i+(Γλ)_i].      (Q5)

Take the actual positive Γ-simplex supplied above. Then

    Σ_(i∈E_c)[(1−n_i)/n_i]γ_i
       ≥ Σ_i s_i+Σ_(i∉E_c)γ_i >0.               (Q6)

Consequently some c-active owner has BOTH positive original finite
mass and positive original Never mass. The contradiction if all such
owners were pure Never is actual: the small fixed-ρ word makes the
graft's limiting full debt strictly belowδ; first chooseρ, then N,
then a sufficiently large original finite index. No Nash tail or
positive-floor hypothesis for a solved test profile is substituted.

### 15. Root/later classification and the literal prefix seam

Call an owner a ROOT BRIDGER if τ and some finite point afterτ both
maximize its full cap. A ROOT-ONLY owner has maximizing set exactly
{τ}. A LATER-ONLY owner does not maximize atτ. Its entire maximizing
set is finite and strictly later, since no test precedes the earliest
active point and Never is strictly below every cap.

The produced q need only be a COMPACT JOINT-LAW/semantic cluster,
not an attained integer-clock profile. Its original finite realizers
can be normalized to literal root0 with EXACT limiting rates a:
censor the vanishing prescribed head before the retained root, then
replace the convergent root rates by a. Product-TV errors vanish.
The removed early response tests paid s_i in the limit, strictly below
B_i by Section8. Retain EVERY subsequent occupied and empty date;
no new empty gap is inserted.

All a_i<1, so actual conditional suffix laws exist eventually. Extract
their complete semantic pairs w^k=(v^k,b^k) to w=(v,b)∈K_all. The
literal root-prefix formula gives

    U_k=a_k Q_k+(1−a_k)(A_k+h_k^root v_k),
    B_k=max(Q_k,A_k+h_k^root b_k),                (Q7)

where h_k^root=∏_(ℓ≠k)(1−a_ℓ), Q_k is the root Quit endpoint, and
A_k sums the passive rewards when some opponent exits at the root.
Every response later than root0 is exactly the corresponding complete
suffix response. Root0 itself is the Quit endpoint. No old earlier
max is lost. Thus(Q7) recovers the ORIGINAL minimum, not a new minimum
chosen by a separate prefix extremum.

This is also the exact tracked quittingTerminalSemanticPrefix formula
and quittingTerminalSemanticPrefix_mem_carrier in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean. Every fixed
root applied to any actual semantic carrier pair is actual-carrier
attainable by tail approximants. The extracted w is NOT asserted to
be a minimum or Nash continuation.

Because every actual suffix opponent-Never product is positive in the
limit and s_k>0, its Never test is strictly below a late finite test.
Consequently the root/later equality in(Q7) is equivalent to having
a FINITE later cap maximizer. A nonbridger has a strict numerical
gap between Q_k and the entire later envelope, even if the latter
has several or nonisolated maximizing points.

### 16. A supported sole bridger is impossible at the rigid paid minimum

Suppose i is the only root bridger and 0<a_i<1. Vary ONLY its numeric
root rate in a two-sided interval, keeping the exact tail pair w and
all other rates fixed. Its own cap branches are independent of a_i.
Every other owner's strict root/later numerical gap persists.
Therefore all FULL caps and the total debt are affine in a_i there.
This uses the full later envelope in(Q7), not one selected late test.

All these pairs belong to K_all. Global minimality at the interior
a_i forces the affine total to be identicallyδ in that interval.
But the own debt is

    d_i(a_i)=(1−a_i)h_i^root(b_i−v_i),

and its original value is d*_i>0. It changes strictly, contradicting
the SAME debt vector at EVERY full minimum. Hence a sole bridger has
a_i=0, since the source has no sure root.

This argument remains valid when other owners are later-only and
their maximizing families are multiple or nonisolated. Their ENTIRE
envelopes are retained in(Q7). It does not assume all caps unique.

### 17. The actual minimum-fibre path in the root-only sole-bridge arm

Suppose i is the sole bridger and every other owner is ROOT-ONLY.
Section16 gives a_i=0. Section14 gives a c-active owner; since c≠τ,
that owner must be i, and E_c={i}. By(Q6) it has 0<n_i<1.
Its OLD finite conditional law F_i therefore exists and has no mass
atτ or before it.

Set m_i=1−n_i, and change ONLY its independent law:

    q_i^s=sF_i+(1−s)δ_Never,       0≤s≤1.         (Q8)

Implement this FIRST on the exact root0 finite realizers from
Section15. Their conditional finite laws have uniformly bounded
density since m_i^k→m_i>0; they have no mass at root0 exactly.
Every other player's actual law is unchanged. No common random
choice between whole profiles, new finite atom, stretch or late
boundary payment is used.

The full old-chart transport in Sections6–7 handles this old finite
submeasure and separate Never atom. At every finite index, every pure
response payoff is affine in s. Uniformly over ALL finite tests and
Never, changing s to t costs at most2M|s−t| by product TV. The compact
old response compiler, including every moving raw cut, therefore gives
a continuous convex full cap B_j(s)=max_X V_j(t,q^s).

For s≥m_i, no old positive finite-mixture atom vanishes: owner i's
finite density increases and all other finite laws stay put. The
same retained finite clock chart handles old atom intervals, their
right cuts and every final finite test. The final c retains zero
mixture mass, and an after-c response has the same value as c.
Only the separate Never atom of owner i vanishes at s=1.
Near m_i on BOTH sides, its finite and Never densities remain positive
as well. Outside that neighborhood the affinity/convexity formulas
can also be obtained directly on the unchanged finite calendars and
passed to the limit, without assumed raw-clock tightness.

Every resulting semantic pair belongs to K_all. At s=1, each actual
owner-i law is surely finite, so actual products absorb; their limiting
pair belongs to K_abs. This is absorption at EACH realizing index,
not an assertion that a compact finite endpoint is an executable clock.

The own cap B_i is fixed on the whole path because the opponent laws
are fixed. Every other owner's root payoff is ALSO fixed, since owner i
has no before-root or root mass under F_i or Never. Thus

    B_j(s)≥Q_j=B_j(original)  for j≠i, all s.      (Q9)

At s=m_i, τ is each such j's UNIQUE isolated maximizing point. The
compact complement X\{τ} has a strict uniform gap. The full TV bound
keeps all those caps EXACTLY at Q_j in a two-sided interval. This
includes c, Never, lower near-cap tests and all moving upper deadlines.

Every cap is therefore fixed locally, while every prescribed U_k(s)
is affine. Total debt is affine, ≥δ, and attainsδ at interior m_i:
it is identicallyδ locally. Common individual debts force

    U_k(s)=B_k−d*_k=U_k(original)

on that interval for EVERY k. Since prescribed payoffs are affine
on the ENTIRE one-coordinate path, they are actually constant for
ALL s∈[0,1]. Payoff preservation is DERIVED from global minimality
and debt rigidity, not supplied as a hypothesis.

#### 17.1. A genuine first cap wall adds a second OWNER

For completeness, this path yields an actual source improvement
even before least-Never selection. By(Q9) every observer cap is
bounded below by its old root cap. The equality set of each convex
B_j(s) with that constant is an interval. Their common equality set
on [m_i,1] is a closed interval extending to the right of m_i.

At s=1 the absorbing floor gives D(1)≥δ+g, so its right endpoint
s* satisfies m_i<s*<1. At s* the ENTIRE semantic pair remains
exactly (U(original),B(original)); this is a true actual-carrier
minimum, not the endpoint value of a selected-response polynomial.

Some observer j≠i acquires another maximizing point at s*: otherwise
the uniform compact complementary gaps would extend the interval.
A test beforeτ still pays s_j<B_j. Never still loses to c by
h_j(s*)s_j>0, since s*<1 and every other n_k>0. The new point
is consequently FINITE and strictly later thanτ, with actual
moving finite-deadline witnesses.

Owner i's old root/later caps remain unchanged, since its opponents
never changed. Owner j's root cap stays Q_j and its new late cap
equals that same value. At least two root rates are positive and
none is sure, so every j has a positive nonempty opponent-root
event S. The two kernels are r_j(S∪{j}) at root and r_j(S) later.
Their within-row distinctness makes the new bridge genuinely different,
not an outcome-equivalent clock alias. Two DIFFERENT OWNERS now bridge.

This is not asserted to be an attained raw integer-clock minimum.
It has actual finite realizers with the same fixed first root; feeding
those back through the source compiler preserves the root rates and
moving late witnesses. All full cap branches were priced before this
regeneration. No further bridge-rank iteration is automatic.

### 18. Least LITERAL joint Never at the SAME final table

For actual independent profiles p, let

    ν(p)=Pr_p(all four prescribed clocks are Never)
        =∏_i p_i(Never).

Define the finite-dimensional augmented carrier

    H=closure{(U(p),B(p),ν(p)): p actual and independent}.

It is compact by bounded rewards and 0≤ν≤1. Its semantic projection
is exactly K_all: for any semantic realizing sequence, a subsequence
of its bounded literal ν values converges. Conversely every augmented
limit has semantic projection in K_all.

The nonempty closed set

    H_min={(U,B,ν)∈H: Σ_i(B_i−U_i)=δ}

is compact. Select its least ν, denoted ν_min. Section9's uniform
actual near-minimum Never floor passes to EVERY point of H_min,
so ν_min>0. The selection is at this SAME r† and δ. No tax extremum,
recipient scaling or further reward perturbation is performed.

#### 18.1. Every regeneration retains the chosen literal probability

Begin with an actual sequence realizing the CHOSEN augmented point.
Censor sufficiently late finite draws to Never to obtain finite
profiles. Choose their total censored mass to vanish with the index.
The payoff and ALL-cap errors vanish by product TV; also

    |ν(censored p)−ν(p)|≤Σ_i censored finite mass_i

by elementary product telescoping. Thus these finite profiles still
realize the chosen augmented minimum, not a different one.

Extract the four literal marginal Never masses n_i^k→n_i. Their
product is ν_min. Common-quantile finite-clock transport and retained
atom refinements in Section6 keep Never as its separate isolated
label, so the marked law has q_i(Never)=n_i EXACTLY. A finite draw
whose RAW date diverges remains a FINITE marked draw; it is never
silently changed into Never. The finite final c is also distinct
from Never and has zero mixture mass.

The universal marked-minimum assertions of Part I apply to THIS
sequence and every retained marked subsequence. They require no
replacement by an independently selected minimum. If exact first
root0 rates are desired, Section15's vanishing head/rate TV errors
also make the ν error vanish. In the root/suffix factorization,

    ν(full profile)=∏_i(1−a_i) · ν(conditional suffix).

Only the FULL ν is ν_min. The conditional suffix need not be minimal
and is NOT assigned ν_min. Raw-time escape, semantic compactness and
conditional survival are therefore kept separate from literal Never.

#### 18.2. The flat old-law path contradicts least Never

Suppose a produced least-Never minimum had a sole bridger i and
three root-only observers. Sections16–17 give a_i=0 and 0<n_i<1,
and provide a two-sided true-minimum interval of(Q8) about m_i.

Choose s>m_i inside that interval. The actual finite realizers have
p_i^{k,s}(Never)=1−s and every other marginal Never mass unchanged.
Their augmented limit still has D=δ and now has literal probability

    ν_s=(1−s)∏_(j≠i)n_j < (1−m_i)∏_(j≠i)n_j=ν_min.

It lies in H_min, contradiction. This is a legal independent
min-fibre change of actual laws. No absorbing law is mistaken for a
full minimum, and no conditional survival coordinate replaces ν.

### 19. Exhaustive source theorem and its exact open alternatives

Produce the marked representative from Section18's chosen triple.
Part I supplies at least one root/later bridging owner. If at least
two DIFFERENT owners bridge, alternative(I) in the theorem holds.

Otherwise let i be the sole one. Section16 gives a_i=0. Every other
owner either maximizes only atτ or does not maximize there. They
cannot all be root-only, by Section18.2. Hence some different j
does not maximize atτ. Since τ was the earliest cap point and
Never is strictly suboptimal, this j's ENTIRE maximizing set consists
of finite points STRICTLY afterτ. This is alternative(II).

No uniqueness, isolation, positive own atom, quietness, positive root
rate or fixed supplied continuation is imposed on this later-only
owner. Its maximizing set may be multiple or nonisolated. The sole
bridger may even have no old finite mass in this residual:
Section17's finite-branch argument used the absence of a later-only
observer, and is NOT transferred to alternative(II).

For every bridging comparison, the fixed positive nonsure root rates
and within-row genericity give the positive-event kernel distinction
proved in Section17.1 and Part I. Every full cap remains unrestricted:
pure finite deadlines and literal Never are all retained, and by
affinity they include every complete unilateral behavioral deviation.

This proves arbitrary counterexample → ONE fresh table → ONE
least-literal-Never full minimum → the stated exhaustive disjunction.
It does not transport an old minimum through a reward change, align
independently selected sources, or claim a playable averaged profile.

The increment over Part I is exclusion of the root-only sole-bridge
arm at the selected least-Never source. A second bridging OWNER or
a genuinely later-only OWNER must remain. This is source narrowing,
not a general debt-decreasing consumer.

### 20. Literal-clock boundary tests for the new steps

The complete boundary tables in Part I Section12 remain part of
this artifact. The following tests isolate the added distinctions.
Every unmentioned nonempty recipient-coalition entry is specified
by the stated rule; live and AllNever pay0.

#### 20.1. A later-only owner is not a quiet root-cap owner

Set all four owns to1, r_0({1})=2, and EVERY other nonempty entry to0.
Let owner1 quit at date0 with probability1/2 and otherwise Never;
all other prescribed owners use Never. The full prescribed vector is

    U=(1,1/2,0,0).

Owner0's root test pays1/2, every finite test after0 pays3/2, and
Never pays1. Owner1's every finite test pays1 and Never pays0.
Owners2 and3 receive1/2 under every finite test and0 under Never.
Thus the ENTIRE cap vector and joint Never are

    B=(3/2,1,1/2,1/2),    ν=1/2,    D=2.

The root response of owner0 is strictly BELOW its cap even though
it has positive own singleton and positive literal Never. This
does not satisfy the source's global minimum or row genericity:
pure grand at date0 is a zero-debt profile. It is only a complete
literal test that root-only cap fixation cannot be assigned to
the later-only alternative.

#### 20.2. Thin words and one common date have different FULL caps

Set owns1, every passive reward2, and EVERY nonsingleton participant
reward3. This specifies all60 coordinates. For λ_i=1/4 and ρ=1/2,
the words in(Q2) have exact limit

    μ_j=1695/16384,
    u_i=11865/16384,
    b_i=681/512,
    D=9927/4096.

The finite tester curve is increasing; late finite dominates Never.
At ONE common date with the same finite probabilities1/8, instead

    Q_i=425/256,
    lateFinite_i=681/512,
    Never_i=169/256,
    U_i=201/256,
    B_i=425/256,
    D=7/2.

The joining test rather than the late solo test sets this cap.
Substituting that one-date cap into(Q3) would keep first-order pair
spikes and invalidate(Q5). This table is already solved by pure grand;
neither positive profile debt is a fictitious global floor.

#### 20.3. Literal full Never is not conditional suffix Never

Set r_i(S)=1 if i∈S and0 otherwise, for ALL nonempty S.
Let all four owners quit at date0 with probability1/2 and otherwise
Never. Its literal full joint Never is1/16. The suffix after root0
is AllNever, whose conditional joint Never is1. The ORIGINAL FULL PROFILE has caps1,
prescribed payoffs1/2, and D=2. The exact product identity is

    1/16=∏_i(1−1/2) · 1,

not ν_full=ν_suffix. Pure grand has debt0; this is not a minimum
source. It tests the probability label retained by Section18.

### 21. Scope and remaining consumer

All uncompiled source, marked transport, end-graft, thin-word and
least-Never mathematics used in this theorem is included above.
The exact checked declarations and their probability modes are
named where used; no conference-note claim is a proof input.

The surviving source is nonsure, fully paid and nonabsorptive.
Alternative(I) requires a coupled intervention pricing at least
two different root/later owner walls. In alternative(II), the
later-only owner's whole envelope may change under finite/Never
conditioning, so fixed caps and payoff preservation no longer follow.
Continuing the first-wall path can immediately raise a newly tied
observer cap. The theorem supplies neither iteration nor a favourable
observer upper price.

No finite-support minimum attainment, raw-calendar tightness,
conditional Nash tail, convex minimum fibre, chronology completion,
periodic equilibrium or uniform-equilibrium payoff is claimed.
Both residual alternatives and the full Fin4 conjecture remain open.

### 22. Lean handoff and exact strategic-input map

This section describes the new ordinary theorem's implementation
boundary. It does NOT name new declarations as already checked.
In particular a semantic carrier alone is insufficient for least
literal Never: its projection can forget which ν an actual sequence
realizes. The augmented carrier and retained joint-law witness are
new proof obligations supplied mathematically in Sections18–19.

The implementation order and uses are:

| Mathematical object/fact | Exact input | Ordinary proof here | Downstream use |
| --- | --- | --- | --- |
| ONE final positive-own generic table, δ,g and common positive d* | Arbitrary Fin4 no-UE hypothesis; original complete behavioral semantics | Part I Sections2–10 | Fix table BEFORE augmented selection; never transport an old minimum through reward changes |
| Augmented H with literal ν and semantic projection K_all | Actual independent stopping laws and ENTIRE (U,B) pairs | Section18 | Compact H_min and attainment of least ν_min>0 |
| Chosen triple preserved by finite approximation | A realizing sequence for THAT triple | Section18.1 | Finite all-response source compiler with ν error→0 |
| Marked minimum retains literal marginal n and their product | The SAME finite realizing sequence, separate Never label, bounded common-chart densities | Part I Section6 and Section18.1 | Positive joint ν_min; first-root normalization still retains the FULL coordinate |
| Sole bridger must have root rate0 | Actual root-prefix formula and common positive debts at EVERY minimum | Sections15–16 | Eliminates supported sole-bridge case even with multiple/nonisolated later-only cap families |
| Old finite branch at the sole/root-only end wall | Positive own rewards, exact end graft, actual positive Γ-simplex, all-clock thin words | Section14 | Supplies m_i,n_i>0 without assuming prescribed finite mass |
| Legal local path preserving FULL semantic pair | Sole bridger plus three root-only cap owners; actual old finite/Never conditioning | Section17 | Produces an augmented minimum with smaller literal ν |
| Exhaustive two-owner/later-only alternative | Least ν_min and the above legal contradiction | Sections18.2–19 | The two genuinely open strategic alternatives in the theorem |

The existing checked semantic carrier/prefix pieces being reused are
quittingTerminalSemanticCarrier, quittingTerminalSemanticPrefix and
quittingTerminalSemanticPrefix_mem_carrier in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean. The new
augmented object must additionally retain ν as an ACTUAL independent
profile coordinate and the finite realizing sequence witnessing its
chosen value. It cannot be defined by freely adjoining an arbitrary
number in [0,1] to a semantic pair.

The implementation's chosen-minimum predicate must say least ν over
EVERY augmented triple of debtδ, not over one fixed semantic fibre
or a selected collection of marked sources. Its source regeneration
must retain that SAME triple. The marked witness must still expose:

- convergence of all U,B and literal marginal Never masses;
- the compact complete finite/Never response test space, retained
  isolated root and final finite c distinct from Never;
- every moving pure-clock witness and bounded old-law transport;
- root rates a and actual fixed-root finite realizer calendars;
- original positive opponent-root events for the kernel comparisons.

The record needed by a strategic consumer contains ONE shared table,
δ,g,d*, ν_min, the chosen augmented minimum and its marked joint law,
the first root and rates, and the exhaustive owner identities from
Section19. Each bridging owner needs root and later finite maximum
tests with positive-event payoff-kernel distinction. A later-only
owner needs its ENTIRE maximizing set strictly later, not one chosen
late test paired with an omitted root maximum.

The conditional suffix pair belongs to the SAME original carrier,
but is not supplied as a minimum or Nash profile. Its literal Never
probability obeys ν_full=∏(1−a_i)ν_suffix, not ν_suffix=ν_min.
The handoff gives no profile attaining the compact minimum on raw
integer clocks and no consumer of the two final alternatives.
