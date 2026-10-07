# Positive terminal-debt minima have a multiple cap or a zero-mass cap clock

## Exact statement

Let I be any nonempty finite player set of cardinality n. For each
nonempty coalition S⊆I fix real rewards r_i(S), with |r_i(S)|≤M for
some M>0. The first finite date with at least one Quit absorbs at its
quitting coalition; perpetual Continue pays zero. Players' private
randomizations are independent. Before absorption the only public
history is all Continue, so an unrestricted behavioral strategy has a
complete stopping law on ℕ∪{Never}. A unilateral deviator may replace
its entire law, without a horizon, memory, support, or hazard restriction.

For an independent stopping-law profile p, write U_i(p) for prescribed
terminal payoff, b_i(p) for the supremum over all unilateral behavioral
responses, and

    D(p)=Σ_i[b_i(p)−U_i(p)],   δ=inf_p D(p).

The same cap is the supremum over ALL pure finite stopping dates and
Never; the same infimum δ results if p is restricted to finite stopping
support, with Never still permitted. Assume δ>0.

From ANY specified finite-law sequence p^k with D(p^k)→δ, the proof
below produces a subsequence, a compact marked finite-test calendar
T⊆[0,c] with c=max T, a separate isolated Never label, and independent
laws q_i on X=T⊔{Never}, such that

    q_i({c})=0,  D_T(q)=δ,
    b_i^T(q)=max_{t∈X}V_i(t,q_-i).

Here V_i is the literal first-coalition payoff when i uses the pure
clock t, and U_i(q) uses the independent prescribed clocks. Finite
points of T retain their actual order and ties. Never is not a last
finite clock. Every limiting pure-response payoff is continuous on X.
The producer retains the ORIGINAL finite witnesses p^k, all their
coalition probabilities, payoffs, and complete caps.

**Theorem.** Every marked minimum obtained by this construction has an
owner i satisfying one of the following alternatives:

1. Its complete cap has at least TWO distinct maximizing TEST POINTS
   in X.
2. Its complete cap has a unique maximizing point τ_i, and
   q_i({τ_i})=0.

The point-mass conclusion is literal. A zero-mass maximizing point may
still lie in the topological support of q_i. Distinct maximizing clocks
are counted separately even when they are outcome-equivalent at q.
The conclusion is unchanged on the extended complete test calendar
X⁺=T⊔{c⁺,Never}, where c⁺ is one empty finite test strictly after c.

This is ordinary mathematics, not a Lean-checked theorem. It is a
necessary restriction on a positive unrestricted terminal gap, not an
equilibrium construction or a positive-gap example.

## Conjecture-facing change

The open global obligation is to consume a true positive full-debt
minimum while controlling every player's unrestricted cap. Unique cap
attainment alone does not discharge that obligation: an accumulation
cut can have arbitrarily close nonmaximizing tests. The present theorem
rules out the precise geometry in which EVERY complete cap is uniquely
attained at a positive prescribed POINT ATOM of its owner. It applies
to arbitrary signed rewards and does not require positive Never masses.

This is a pointwise restriction on the produced minimum, not merely
existence of another minimizer with different support. At least one
multiple-maximizer or zero-own-point-mass owner must remain. The theorem
does not exclude genuinely responsive multi-cap cycles, a unique
zero-mass accumulation cut, or a unique zero-mass finite/Never response.

The terminal-gap restriction is conjecture-facing for Fin4: all debts
are nonnegative, so maximum debt E and summed debt satisfy
E≤D≤4E. If δ=0, finite laws have vanishing unrestricted exploitability;
their bounded payoff vectors have a convergent subsequence. The checked
finite-menu target criterion cited below turns this sequence into a
uniform-equilibrium payoff. Thus a game without any such payoff has
δ>0 and must obey the stated marked-cap restriction. The new theorem
does not supply the final consumer of either surviving alternative.

## Strategic inputs and definitions

Only the arbitrary reward table and the positive-gap hypothesis are
inputs. A finite minimizing sequence is chosen from the definition of
the infimum. The marked calendar, all prescribed laws, cap functions,
retained atom intervals, and the original finite realizing sequence are
produced below. No equilibrium, root rates, minimizing continuation,
selected best-response distribution, or law annotation is supplied.

For an ordered finite or compact calendar, an independent pure clock
tuple yields its earliest finite coalition; if no finite clock occurs,
all rewards are zero. Prescribed payoffs are integrals of this bounded
kernel against the product law. For player i, V_i(t,p_-i) is the same
integral with its own factor replaced by the point mass at t. A mixed
unilateral law integrates these pure values, so its supremum equals
their supremum. Prescribed own laws are among the allowed deviations;
all debts are therefore nonnegative.

## Source correspondence

The exact tracked declarations inspected are as follows. They supply
the stated original-game semantic facts under their imports; they do
not check the new marked producer or its cap-atom exclusion.

- `abs_expectedPayoff_censorLateFiniteStoppingLaws_sub_le` and
  `abs_replacementCap_censorLateFiniteStoppingLaws_sub_le` in
  `UniformEquilibrium/Quitting/Paths/LateFiniteStoppingLawCensor.lean`
  bound payoff and complete-cap change when all late finite mass is
  moved to Never. They have no reward-sign or normality hypothesis.
- `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
  and
  `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
  in
  `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`
  identify the full law-replacement cap with the unrestricted behavioral
  envelope. The payoff correspondence is supplied there by
  `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
  `quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`.
- `quittingTerminalOutcomeMass_stoppingLawMixture_eq` and
  `quittingTerminalPayoff_stoppingLawMixture_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`
  establish complete-outcome and every-payoff affinity under a one-law
  probability mixture. The multiaffine polynomial below is the integral
  version of this fact. The existing declarations assume coefficients
  in [0,1]; the two-sided signed OLD-ATOM transport is proved separately.
- `exists_finiteDeadlineTimingProfile_approximation` and
  `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  in
  `UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`
  give actual finite-menu approximation and the target-payoff uniform
  criterion with full unrestricted exploitability, not restricted-menu
  regret. The same finite law controls payoff and full exploitability.

The new content is the self-contained marked-calendar representation
needed here, its two-sided reweighting toward EXISTING positive own
atoms with complete actual finite witnesses, and the resulting cap
geometry exclusion. No paper theorem or external source is required.

## Proof

### 1. Finite-law and all-behavioral infima agree

For any stopping-law profile p, replace each player's finite mass after
K by Never. Let a_i(K) be that moved mass; a_i(K)→0. Independent coupling
changes a prescribed outcome only when at least one changed finite draw
occurs. Consequently

    |U_i(p^K)−U_i(p)|≤2MΣ_j a_j(K).

For ANY unilateral pure response the same coupling uses only opponent
changes, giving a uniform bound 2MΣ_{j≠i}a_j(K). Taking suprema gives
the same bound for |b_i(p^K)−b_i(p)|. Hence every complete cap, payoff,
and summed debt converges, proving equality of the two infima. This
argument keeps arbitrarily late finite responses and Never distinct.
Choose finite p^k with D(p^k)→δ.

### 2. Old quantile charts retain all atoms and test points

Put μ^k=Σ_i p_i^k/n. In chronological order assign every supported finite
date, followed by Never, an interval in [0,1] of length its μ^k mass.
Zero-length intervals are omitted. For a supported date a, define on
its interval

    r_i^k(u)=p_i^k({a})/μ^k({a}).

These are coordinate charts only, not a shared random signal. The
players still draw independent coordinates. They satisfy

    0≤r_i^k≤n,  Σ_i r_i^k=n a.e.,  ∫r_i^k=1.

Since L¹[0,1] is separable, bounded weak-* compactness in L∞ supplies a
common subsequence r_i^k⇀*r_i, with the same bounds and integrals.
Let c_k=1−μ^k({Never}); pass to c_k→c. Let E_k be all interval
endpoints, including 0,c_k,1. For EVERY actual finite response date t,
assign its OLD location

    x_k(t)=μ^k({a:a<t})+μ^k({t})/2.

Thus a supported date is at its atom midpoint, an empty date at a cut,
and every date beyond the final finite support at c_k. These locations
have a finite set T_k. Never remains a separate label, not location c_k.
Pass to Hausdorff limits E_k→E and T_k→T. The sets are compact,
T⊆[0,c], c∈T, and 0,c,1∈E. No E point is inside the limiting Never
interval (c,1).

Every component J=(a,b) of [0,c]\E is the limit of ONE original atom
interval J_k=(a_k,b_k): any compact subinterval of J eventually contains
no endpoint, hence lies in one atom; Hausdorff convergence forces its
endpoints to a,b. The only available test in that open interval is its
midpoint. Therefore

    T∩J={(a+b)/2}.                              (1)

The limiting r_i is constant almost everywhere on J: for two compact
subintervals inside J, r_i^k is the same constant on both for large k;
weak-* convergence identifies equal limiting averages. Exhaust J.
The same argument gives constancy on (c,1) when nonempty.

The part of E∩[0,c] outside T is null. Indeed, any component of the
complement of T has at most one E point: two distinct endpoints there
would force an original atom midpoint between approximating endpoints,
contradicting the positive distance from T. There are only countably
many complement components. Define π almost everywhere by collapsing
each J to its midpoint, keeping the remaining E∩[0,c] points, and
sending (c,1) to Never. Set

    q_i=π_*(r_i du).

The average law is π_*du. Its ONLY positive finite point atoms are the
retained component midpoints (1), which are isolated in T by half their
interval length. The endpoint c is not such a midpoint, so q_i({c})=0.
Every other finite point has zero mixture mass and zero own mass.

### 3. Prescribed outcomes and complete caps converge

Let π_k be the original interval-collapse maps. Product densities
R^k(u_1,…,u_n)=∏_i r_i^k(u_i) converge weak-* in L∞ of the product
cube to R=∏_i r_i(u_i). For rectangle indicators this is exactly the
product of marginal weak-* identities. Finite sums of rectangle
indicators are dense in L¹, and all product densities are bounded by
n^n, so the identity holds for every fixed L¹ test. The same holds
for each opponent product with n−1 factors.

Let K_S^k be the first-coalition indicator in these OLD coordinates,
including the all-Never outcome, and K_S its limiting counterpart.
Then K_S^k→K_S almost everywhere and in L¹. Exclude the countably many
retained interval endpoints, c, and equality of two independent raw
Lebesgue coordinates. Two remaining finite coordinates either belong
to the same retained J, hence eventually the same original J_k, or
have a limiting endpoint strictly between them, hence eventually
different ordered original atoms. Their order and tie relation cannot
change. Membership in the separate Never interval stabilizes as well.

Split the integral difference as

    ∫K_S^kR^k−∫K_SR
      =∫(K_S^k−K_S)R^k+∫K_S(R^k−R).           (2)

The first term is bounded by n^n times the L¹ kernel difference;
the second is a FIXED-kernel weak-* test. Both vanish. Thus coalition
laws, prescribed payoffs, and joint-Never probabilities converge.

For caps consider ANY sequence of finite pure tests with OLD locations
x_k→x∈T. At a retained midpoint x, (1) forces x_k eventually to be its
corresponding original midpoint, preserving its exact tie. At every
other x, π_*du has no atom, so the moving-response opponent kernels
converge almost everywhere and in L¹: order comparisons stabilize off
the null set with collapsed coordinate x. Retained atoms adjacent to
x stay on the correct side because their midpoint is separated from
the endpoint. Apply the opponent version of (2). This includes x=c,
which is the final finite response and not Never. The separate Never
kernel converges by its interval membership.

The limiting response payoff is continuous on T. At a retained midpoint
this is automatic from isolation; at every other point the same
zero-atom cut argument with fixed limiting laws gives continuity.
Never is isolated, so continuity holds on X. Compactness gives cap
attainment. Original caps are maxima of finitely many response
functions, including late finite and Never. Extract any sequence of
their maximizing OLD locations to prove limsup b_i(p^k)≤b_i^T(q);
approximate a limiting maximizer by T_k, or retain Never, to prove
the reverse liminf. Consequently

    U_i(p^k)→U_i(q),  b_i(p^k)→b_i^T(q),
    D_T(q)=δ.                                  (3)

This completes the actual-data marked producer used by the theorem.

### 4. A unique positive own-atom cap has a uniform complete gap

Suppose, toward contradiction, that EACH player i has a unique cap
point τ_i∈X and m_i=q_i({τ_i})>0. If τ_i is finite, positive own mass
implies positive mixture mass, hence τ_i is a retained midpoint (1),
isolated in T. If τ_i=Never, it is isolated by definition. Thus
X\{τ_i} is compact. Continuity and UNIQUE POINT attainment imply

    g_i:=b_i^T(q)−max_{t∈X\{τ_i}}V_i(t,q_-i)>0. (4)

Own mass does not constrain opponent payoffs; it supplies topological
isolation in the produced calendar. Generic uniqueness at an
accumulation point would not imply (4).

Independently reweight the EXISTING own atoms by

    q_i^λ=(1−λ_i)q_i+λ_iδ_{τ_i}.                (5)

For −m_i/4<λ_i<1 these are probability laws: every other mass has
positive factor 1−λ_i, and target mass is
m_i+λ_i(1−m_i)>0. A coordinate with m_i=1 simply has zero direction.
Total variation change is at most |λ_i|. Uniformly over ALL pure tests,

    |V_i(t,q_-i^λ)−V_i(t,q_-i)|
        ≤2MΣ_{j≠i}|λ_j|.                       (6)

Choose an open box about zero with all laws legal and
4MΣ_j|λ_j|<min_i g_i. Every complete cap then stays uniquely at τ_i.

Include the additional last finite response c⁺ explicitly. Each τ_i
is different from c, since q_i({c})=0. Therefore q_i^λ({c})=0; no
prescribed mass is added beyond c or at c⁺. Quitting at c and at c⁺
has identical outcomes: any finite opponent exit is strictly earlier,
and on all-opponent-Never the deviator is the sole quitter. Hence

    V_i(c⁺,q_-i^λ)=V_i(c,q_-i^λ).              (7)

This identity is valid for signed rewards and selected Never atoms.
Both tests are below the unique τ_i by (4),(6). The full cap remains
unchanged on X⁺; neither finite test is identified with Never.

### 5. The signed laws have ORIGINAL actual finite witnesses

Nonnegative-mixture affinity alone does not authorize negative λ.
For a finite τ_i, let J_{i,k}→J_i be its retained ORIGINAL atom
interval, of positive limiting length, and let τ_i^k be that original
date. For τ_i=Never use J_{i,k}=(c_k,1)→(c,1)=J_i. Positive own
Never mass ensures 1−c>0. Bounded weak-* convergence, interval
endpoint convergence, and the retained interval constancy give

    m_i^k=p_i^k({τ_i^k})→m_i>0.                (8)

For large k, m_i^k≥m_i/2. For any FIXED λ in the above box, define
the literal independent finite laws on the UNCHANGED original calendar

    p_i^{k,λ}=(1−λ_i)p_i^k+λ_iδ_{τ_i^k}.       (9)

They are nonnegative: away from τ_i^k the factor is positive, and at
that target their mass is at least m_i/2−m_i/4=m_i/4. They integrate
to one. Never remains Never. No new clock or correlated random flag
is introduced, and every original finite response is retained.

Their densities on the OLD chart are exactly

    r_i^{k,λ}=(1−λ_i)r_i^k
                   +λ_i 1_{J_{i,k}}/|J_{i,k}|. (10)

The normalized interval indicators converge strongly in L¹, their
limiting lengths being positive. These nonnegative new densities are
uniformly bounded, for instance by
|1−λ_i|n+2|λ_i|/|J_i| for sufficiently large k, and converge weak-*
to the corresponding density of q_i^λ. Products converge weak-* by
the rectangle argument. The OLD collapse maps, test sets, and outcome
and moving-response kernels are unchanged. The bounded-density split
(2) thus proves convergence of prescribed outcomes and payoffs.

For caps, take any sequence of original maximizing response locations;
extract a limit in T or the separate Never label and apply the same
moving-kernel argument. Approximate every fixed T-test for the reverse
bound. No new mass is inserted at the last finite c; by (7) the limit
caps also agree with those on X⁺. Therefore

    U_i(p^{k,λ})→U_i(q^λ),
    b_i(p^{k,λ})→b_i^T(q^λ)=b_i^{T⁺}(q^λ).     (11)

Each (9) is actual finite, so D(p^{k,λ})≥δ. Taking limits yields

    D_T(q^λ)≥δ                                (12)

for EVERY fixed λ in the TWO-SIDED open box. This is a source-mode
global comparison with explicit finite witnesses, not a variation of
unrealizable payoff/cap annotations.

### 6. The fixed-cap multiaffine branch is impossible

Within this open box all complete caps stay at the displayed τ_i, so

    D_T(q^λ)=F(λ)
       :=Σ_i[V_i(τ_i,q_-i^λ)−U_i(q^λ)].        (13)

F is a multiaffine polynomial: each fixed-response payoff is affine
separately in each opponent law, and each prescribed payoff is affine
separately in every law. Thus every scalar λ_i occurs with degree
at most one in every monomial. Equations (3),(12),(13) give an
INTERIOR local minimum F(0)=δ.

A multiaffine polynomial with an interior local minimum is constant.
If not, take its lowest nonzero homogeneous Taylor part H_k,
1≤k≤n. Every monomial is nonconstant and square-free. Its mean over
the independent sign cube {−1,+1}^n is zero; those distinct monomials
are linearly independent on that cube. Some sign vector h therefore
has H_k(h)<0. For sufficiently small ε>0,

    F(εh)−F(0)=ε^kH_k(h)+O(ε^(k+1))<0,

contradicting local minimality. Identically zero coordinate directions
do not invalidate this argument.

However, the displayed polynomial has the algebraic endpoint

    F(1,…,1)=0.                                (14)

Each prescribed own law at that endpoint is δ_{τ_i}; its displayed
response τ_i is exactly the same law. Thus every summand in (13)
vanishes, including simultaneous ties and Never. Since F(0)=δ>0,
F is NOT constant. The negative Taylor direction exists, and may be
chosen inside the cap-stable legal box.

Crucially, (14) evaluates only the DISPLAYED FIXED-RESPONSE POLYNOMIAL.
It does not assert that τ_i remain caps at λ=(1,…,1), that the actual
endpoint debt is zero, or that the pure tuple is an equilibrium. The
identity is used solely to establish that the LOCAL cap branch cannot
be a constant positive polynomial.

For the chosen εh let η=δ−D_T(q^{εh})>0. By (11), some sufficiently
large ORIGINAL finite witness (9) has

    D(p^{k,εh})<δ−η/2,

contradicting the true global infimum. This is a literal finite-amplitude
coupled change of existing own atoms and all remaining old mass with
every complete response controlled. The assumed geometry is impossible.
Since every cap is attained, its exact negation is the theorem's two
alternatives. ∎

## Boundary tests

### A zero global gap permits unique supported caps

Take four players and r_i(S)=1 if i∈S, and 0 otherwise. If every player
quits surely at date zero, U_i=1. Quitting at zero pays 1; ANY later
finite date and Never pay 0 because the other players have already
absorbed. Every cap is uniquely at its own positive-mass date zero.
All debts are zero, so δ=0. Thus the hypothesis δ>0 is indispensable;
unique supported cap geometry is not impossible by itself.

### Positive PROFILE debt cannot replace the true global infimum

In the same exact table, give every player half mass at date zero and
half at Never. The date-zero response pays 1; every later finite
response pays 1/8, and Never pays 0. Hence each cap is uniquely at the
supported date zero. Prescribed payoff is 1/2 per player, so D=2.

The legal simultaneous old-law change

    p_i^λ=(1−λ_i)p_i+λ_iδ_0

has U_i=1/2+λ_i/2, cap 1, and

    D(p^λ)=2−(1/2)Σ_iλ_i

for λ near zero. Taking all λ_i=1/4 gives D=3/2<2. Negative small
coefficients are also legal because the old target mass is positive.
This exact descent shows why a positive supplied profile debt is not
the positive global δ required by the theorem.

### Zero point mass need not mean outside topological support

Use the same four-player table on the compact calendar T=[0,1], with
each prescribed clock independently uniform on [0,1] and no Never mass.
This is the marked limit of independent uniform finite-grid laws.
For every i,

    V_i(t,q_-i)=(1−t)^3,  0≤t≤1,
    V_i(Never,q_-i)=0.

The cap is uniquely at t=0, but q_i({0})=0 although 0 belongs to the
topological support of q_i. Other tests approach the cap with no
uniform gap. Prescribed U_i=1/4 by symmetry, so D=3; the table's true
gap remains zero. This is an exact topological boundary test, not a
positive-gap example. It also falsifies the invalid replacement of
positive point mass by mere topological support in the isolation step.

## Adapter and consumer

For any arbitrary signed Fin4 table with no uniform-equilibrium payoff,
the checked terminal/full-cap finite-menu criterion implies δ>0 as
explained above. Choose any finite-law minimizing sequence. Sections
2–3 produce a marked minimum from that SAME sequence. Sections 4–6
exclude unique positive-own-point-mass caps for all owners and supply
an actual finite witness below δ if that geometry were present.

The output is the necessary multiple-point/zero-own-point-mass cap
alternative. No further strategic input is supplied or assumed. There
is no downstream full-equilibrium consumer of the surviving alternative
in this result; that remains the actual open obligation.

## Lean handoff

A narrow implementation would formalize the marked producer with its
bounded old densities, retained atom intervals, original test-location
sets, and prescribed/moving-response kernel convergence. It must not
assume the desired point-atom exclusion as a structure field.

The next declarations should establish: positive own finite point mass
is an isolated marked test; unique complete cap at an isolated test has
a uniform complement gap; two-sided old-atom reweightings yield actual
finite laws and full cap convergence; caps stay at their displayed
tests in a two-sided neighborhood; a multiaffine branch with an interior
local minimum is constant; and the selected-response branch at all-pure
displayed clocks is zero. The existing one-law affinity declarations
handle ordinary probability mixtures; signed coefficients still need
the direct nonnegative-law/density argument.

Useful finite checks are the unique-cap δ=0 grand-coalition profile and
the exact half-Quit/half-Never descent above. The formal statement must
retain distinct c, c⁺, and Never labels and must not rewrite the distant
branch-polynomial zero as actual zero terminal debt.

## Scope and nonclaims

There are no reward-sign, own-singleton positivity, positive-Never,
Nash-root, minimum-tail, or finite-memory assumptions. The marked law
need not be an ordinary ℕ law. Only each chosen variation has its own
actual original finite realizing sequence.

This result does not produce a uniform equilibrium, dispatch a responsive
cap cycle, exclude unique zero-own-point-mass maximizers, or exhibit an
unrestricted positive terminal gap. It makes no claim that unique point
attainment at an arbitrary non-isolated test gives a uniform gap. It
does not identify distinct equivalent clocks, or differentiate an outer
infimum over laws using a current minimizing selector.
