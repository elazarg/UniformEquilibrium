# Worst-SUM reward selection leaves atomic-earliest multi-unsupported or multiple-cap sources

## 1. Exact theorem and status

This is a complete ordinary-mathematical proof candidate. The actual
marked-source producer, negative-parameter conditional transport and
simultaneously active-cap comparison are proved below. No supplied
Nash continuation, minimizing conditioned tail or unidentified
strategic source is an input. It is not a full Fin4 UE theorem.

Let I={0,1,2,3}. A reward table assigns r_i(S)∈ℝ to every owner i
and nonempty coalition S⊆I; all-Never pays zero. Prescribed strategies
are INDEPENDENT complete stopping laws on ℕ⊔{Never}. Their first
finite tied coalition determines the reward. A deviation replaces
one owner's COMPLETE behavioral strategy, equivalently its stopping
law. Pure cap tests include EVERY finite date and Never, not a
bounded controller or prescribed finite response menu.

For payoff U_i, response payoff V_i(t,p_-i) and full cap
B_i=sup_t V_i(t,p_-i), put

    D_r(p)=Σ_i[B_i(p)−U_i(p)],
    Δ(r)=inf_(all actual independent stopping laws p) D_r(p).

If ANY signed Fin4 game has no uniform-equilibrium payoff, there is
ONE fresh table r̂ with all sixty entries in [−1,1] and Δ(r̂)=d>0
with this property: apply Section 3 to ANY finite-law minimizing
sequence, and take ANY subsequence satisfying its stated
convergences. At EVERY resulting marked global minimum q, either

- some cap has at least two distinct maximizing compact TEST POINTS;
  or
- all four caps have unique maximizing points τ_i, NOT ALL cap dates
  are equal, at least TWO owners have zero OWN point mass at their
  respective caps, and the earliest cap τ=min_i τ_i is a finite
  ISOLATED positive MIXTURE atom. At least one owner maximizing at
  this earliest point has zero own mass there.

“Not all cap dates equal” does NOT mean pairwise distinct. Several
unique cap owners may share a date. “Unsupported” below means ZERO
OWN POINT MASS, not exclusion from topological support. The earliest
mixture atom may be supplied by an owner whose own cap is later.
No all-unique source with only one unsupported owner remains.

Section 7 also proves a UNIVERSAL restriction for arbitrary bounded
signed tables at ANY produced positive global minimum, without cap
uniqueness: its earliest active response is finite. If that point has
zero MIXTURE mass, some prescribed owner stops strictly before it
surely, and each of the other three caps maximizes at that point,
finite c and Never. Thus the zero-mixture earliest branch has genuine
multiple caps; it cannot hide a unique nonisolated earliest observer.

The table is selected ONCE before any new minimizing law, cap family
or owner geometry. This is an existential counterexample-class
reduction, not a pointwise restriction on every original table, a
positive-gap example, or an equilibrium producer. Multiple caps and
all-unique sources with at least two unsupported owners at the stated
atomic earliest point remain OPEN.

The distinct eight-coordinate subtheorem in Section 10 preserves ALL
singleton rewards and excludes exceptional-latest unique-cap sources.
The expanded construction changes own singletons and must not inherit
that preservation claim.

## 2. Original-game correspondence and the positive-gap input

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

Positive scaling multiplies every payoff, cap, debt and Δ by the same
factor. Divide any positive-gap finite table by a positive reward
bound. Thus existence of any Fin4 no-UE table implies existence of a
positive-Δ table in the closed sixty-coordinate unit cube. No reward
sign, punishment normality, singleton normalization or single-pivot
condition is assumed.

## 3. Actual finite sequences produce the marked global source

Fix a finite reward bound M and δ=Δ(r)>0. First, finite-support
stopping laws have the SAME infimum. Move each owner's finite mass
after K to Never, writing a_i(K) for the moved mass. Independent
coupling changes prescribed outcomes only if a changed draw occurs,
so every prescribed payoff changes by at most 2MΣ_j a_j(K). For
ANY response of i, the same bound uses only opponent changes, uniformly
over all finite responses and Never. Taking suprema gives complete-cap
convergence. Since a_i(K)→0, D converges and the infima agree.
Choose finite profiles p^k with D_r(p^k)→δ.

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

## 4. Signed old-law variation and its complete realization

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
kernels are unchanged. The Section 3 product and kernel argument
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
at λ=1 when its positive mass is fixed, a fact used in Section 7.

## 5. Two cap-stability mechanisms and the polynomial principle

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

## 6. Supported earliest groups force the grand-withdrawal identity

First, four unique supported caps are impossible: reset each owner
toward its own positive atom. All caps have isolated uniform gaps,
and the all-one selected-response endpoint in (6) is zero, since each
owner prescribes its displayed response. Constancy would give δ=0.

Now partition I into nonempty J and L, with all J caps supported and

    h=max_(j∈J)τ_j < min_(ℓ∈L)τ_ℓ.

There is NO mass assumption on later L caps. Put t₀=min_(j∈J)τ_j.
If every ℓ∈L has e_ℓ=q_ℓ(clock>t₀)>0, reset J toward their supported
cap atoms and L toward their old conditional laws after t₀. J caps
stay fixed by isolation. For each L cap, opponent expansion using
(5) has only early terms ≤h, so (4) and the lower compact gap fix
every L cap, even nonisolated ones. Section 4 realizes the signed
changes through the original RIGHT cut of the retained t₀ interval.
At the all-one endpoint J prescribes its cap dates, while every L
law and displayed response lie after the sure J exit at t₀. All
selected debts vanish. This contradicts δ>0.

Therefore some m∈L stops no later than t₀ surely. Every J cap must
equal t₀: a later displayed response would tie Never due to m's
sure earlier exit. Also q_m(t₀)>0: otherwise m stops strictly before
t₀ and each J cap would tie Never. No second owner ℓ∈L can exist.
A finite later τ_ℓ would tie Never; if τ_ℓ=Never the distinct finite
test c>t₀ ties it. Consequently L={m}, J has three owners,
q_m(τ_m)=0 and all τ_j=t₀<τ_m.

All four original laws have positive own atoms at t₀. Reset them
toward this atom. The J caps remain fixed by isolation; m's later
cap remains fixed by (4). The algebraic all-one endpoint is pure
grand absorption at t₀. The J selected debts are zero, while m's
later response receives the omitted triple instead of grand. Hence

    δ=a_m(r), a_m(r)=r_m(I∖{m})−r_m(I).           (7)

This is the exceptional-latest (LC) identity, including its sure
boundary, not an assertion of pure-grand Nash or minimum-tail status.

For the general order classification, let J be the EARLIEST cap group.
If every J owner has positive own mass, then either J=I, contradicted
by the all-supported argument, or the separated partition above
applies regardless of mass or interleaving among later owners. Thus
EVERY all-unique minimum either has an earliest zero-own-mass owner,
or has exactly LC geometry and identity (7).

## 7. Simultaneously active caps exclude a zero-mixture earliest point

The checked declaration `minimumTerminalSemantic_singletonMargin`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
has these exact inputs: a pair in the ORIGINAL actual semantic
carrier, total debt no larger than that of EVERY pair in that carrier,
and STRICTLY positive total debt δ. It concludes, for EVERY owner,

    δ≤B_i−s_i, s_i=r_i({i}).                         (8)

It is under the file's stated imports. No tail Nash, reward sign,
punishment normality, selected-response attainment or singleton
normalization is assumed. Section 3 supplies all of its source-pair
hypotheses; below it is applied again only AFTER the final conditioned
pair is proved to have its actual full caps and actual debt δ.

This argument handles arbitrary MULTIPLE active responses and distinct
later cap dates. It does not presume unique maxima, supported selected
clocks or minimizing conditional tails.

For each owner let A_i be the nonempty compact set of ALL maximizing
points of its continuous full response function on X=T⊔{Never}.
Let τ=min(⋃_i A_i), with Never ordered after every finite tester.

First, τ cannot be Never. Otherwise every A_i={Never}. If some own
Never mass is zero, that owner stops finitely surely, so for every
OTHER recipient finite c and Never have identical payoffs and are
both maximizing, contradicting earliestness. If all own Never masses
are positive, four supported unique caps are excluded by Section 6.
Thus τ is finite.

Suppose the mixture mass at τ is zero. If some owner h has
q_h(clock>τ)=0, then q_h(clock<τ)=1. For every i≠h, any response
t≥τ gives the same first-coalition payoff because h exits strictly
earlier surely. Since i has a maximizing point τ_i≥τ, ALL such
upper responses maximize its cap. In particular τ,c,Never are
maximizing POINTS; if τ=c there are two distinct points, otherwise
three. This is the precise sure-early obstruction, not Nash of those
owners or permission to replace h by a pure early clock.

It remains to exclude the case

    q_i({τ})=0, e_i=q_i(clock>τ)>0 for EVERY i.       (9)

If τ is the first finite tester, V_i(τ)=s_i for all i. At least
one owner m has τ∈A_m; (8) gives δ≤B_m−s_m=0, contradiction.
Otherwise take real ordered cuts u_n<τ increasing to τ and put

    e_i^n=q_i(clock>u_n)≥e_i,
    ν_i^n=q_i(·|clock>u_n).

For each FIXED n change all four existing laws independently by
q_i^λ=(1−λ_i)q_i+λ_iν_i^n on an open two-sided legal box.
Its early and late likelihood factors are 1−λ_i and
c_i=1+λ_i(1/e_i^n−1)>0. Equivalently,

    q_i^λ=c_i q_i−(λ_i/e_i^n)E_i^n,
    E_i^n=q_i|_(clock≤u_n).

Every nonoriginal term in any opponent product contains an early
finite submeasure. It has absorbed before EVERY response t>u_n,
including Never. Therefore the SAME test-independent constant works
for the entire upper response family:

    V_i(t,q_-i^λ)=k_i(λ)V_i(t,q_-i)+C_i(λ),
    k_i(λ)=∏_(j≠i)c_j>0, t>u_n.                    (9a)

Choose u_n<a_n<τ. The compact lower set T∩[0,a_n] contains NO
active point for ANY owner, by the definition of earliest active
point. Each owner has a strictly positive uniform lower gap, preserved
on a smaller signed box by total-variation control. All its active
points are above a_n and stay tied under the positive affine map
(9a). Thus its COMPLETE cap on that box equals k_i B_i+C_i.

This fixes ALL upper active responses simultaneously, even infinitely
many or nonisolated ones; it is not the false assumption that one
arbitrary branch controls a changing maximum. The gaps and legal box
may depend on n. No uniform gap or uniform box as n→∞ is needed.

Choose once any τ_i∈A_i, with τ_m=τ for one earliest owner m.
The signed selected sum

    F_n(λ)=Σ_i[V_i(τ_i,q_-i^λ)−U_i(q^λ)]

is multiaffine and equals actual D≥δ on that box, with F_n(0)=δ.
Section 5 gives algebraic F_n≡δ. At all-one this yields ONLY

    Σ_i[V_i(τ_i,ν_-i^n)−U_i(ν^n)]=δ.               (9b)

Here the actual finite seam is Section 4's direct old-cut construction.
Strict-after a retained atom uses its RIGHT endpoint; a zero-mass
boundary has a null raw preimage and converging old endpoint cuts.
Real cuts outside T specify the same initial segment at the appropriate
retained boundary. The original modified density is exactly

    f_i^k[(1−λ_i)+(λ_i/e_i^{k,n})1_(old clock>cut)].

Cut indicators converge strongly in L¹, normalizers converge to
e_i^n>0, and the signed likelihood factors stay nonnegative and
bounded. The fixed-test weak-* calculation, independent rectangle
product tests and unchanged prescribed/ALL-moving-response kernels
prove complete payoff and cap convergence. Negative parameters are
actual probabilities, not a citation to forward affinity. Original
Never remains included, c mass stays zero, and c⁺ duplicates c.

Since there is no atom at τ and all FINAL e_i>0, ν_i^n converge in
TOTAL VARIATION to ν_i=q_i(·|clock>τ). The final ν has direct
old-cut realization at the null τ boundary, with bounded densities
at most the original bound divided by min_i e_i. Section 4 puts
its COMPLETE pair in the original carrier. Uniform response/payoff
bounds pass (9b) to the selected identity

    Σ_i[V_i(τ_i,ν_-i)−U_i(ν)]=δ.                    (9c)

The next ALL-response calculation is essential; (9c) alone does not
make ν another minimum.

Write E_j=q_j|_(clock<τ), so ν_j=(q_j−E_j)/e_j. Every product term
containing an E_j exits STRICTLY before every t≥τ, INCLUDING τ
itself. Consequently

    V_i(t,ν_-i)=k_i V_i(t,q_-i)+C_i,
    k_i=∏_(j≠i)e_j⁻¹>0, t≥τ,                       (9d)

with one common C_i on the CLOSED upper set. Because each original
τ_i is a global maximizer and τ_i≥τ, (9d) bounds EVERY upper
response by V_i(τ_i,ν_-i). At τ all conditioned opponents are later,
so V_i(τ,ν_-i)=s_i; hence V_i(τ_i,ν_-i)≥s_i. Every finite response
below τ also pays exactly s_i. Never lies in the upper set, and
c⁺ duplicates c. Thus the ACTUAL full caps satisfy

    B_i(ν)=V_i(τ_i,ν_-i) for ALL i,
    B_m(ν)=V_m(τ,ν_-m)=s_m.                         (9e)

Distinct later owners' caps may exceed their singleton rewards.
Only ONE earliest equality is needed. Equations (9c),(9e) give
ACTUAL D(ν)=δ. Carrier membership makes ν a true global minimum,
and (8) at owner m now gives δ≤B_m(ν)−s_m=0, contradiction.

We have proved: at a positive produced minimum a zero-mixture
earliest cap forces a sure-strictly-earlier prescribed owner and
multiple upper caps for all three other recipients. In particular,
if ALL caps are unique, their earliest maximizing point has positive
mixture mass and is finite and isolated by Section 3. A nonisolated
earliest unique observer cap is therefore impossible. This result
does not equate zero OWN mass with zero MIXTURE mass.

## 8. Common positive-atom caps have a finite join-sum value

Suppose all four unique caps share one point τ and define
A={i:q_i(τ)>0}. The cases A=I and A=∅ were excluded above. For
∅≠A⊊I, τ is finite or Never. Never is impossible: any owner outside
A has no Never mass, hence stops finitely surely, making every other
Never cap tie the finite c test. Thus τ is finite, a positive mixture
atom and isolated for ALL four recipients.

For each z∉A, q_z(clock>τ)>0; otherwise z stops strictly before τ
and every other displayed τ cap ties Never. Reset A toward its
supported atom τ and its complement toward old conditional laws after
τ. The uniform isolated gaps fix all caps on a legal signed box,
with the RIGHT retained-cut realization of Section 4. At the
all-one selected endpoint A exits surely at τ, while outsiders
prescribe late laws. Supported debts vanish; each outsider's displayed
response joins A rather than following it. Hence

    δ=C_A(r),
    C_A(r)=Σ_(z∉A)[r_z(A∪{z})−r_z(A)].           (10)

The individual terms need not all be positive. Equation (10) is not
an actual Nash or debt assertion at the distant endpoint.

## 9. A sole unsupported owner: early, tied, and late cases

Suppose all caps are unique, exactly one owner m has q_m(τ_m)=0,
and the other three have positive own cap atoms. Put
t₀=min_(j≠m)τ_j. If τ_m>t₀, the earliest supported-group argument
of Section 6 forces exactly LC, hence (7).

If τ_m=t₀, let H={j≠m:τ_j=t₀}. This nonempty supported atom
isolates τ_m, so all four unique caps have uniform gaps. The clock
t₀ is finite: otherwise the unsupported m stops finitely surely,
making each supported Never cap tie c. Also q_m(clock>t₀)>0:
otherwise m stops strictly before t₀ and H caps tie Never. Reset
the supported owners toward their cap atoms and m toward its old
conditional law after t₀. At the constant selected endpoint only
m's debt survives. Its response joins H, while its prescribed law
follows H. Therefore

    δ=J_(m,H)(r),
    J_(i,K)(r)=r_i(K∪{i})−r_i(K).                 (11)

This is an INDIVIDUAL join, not C_H when supported owners have later
caps. The right-cut transport is legal and all cap gaps are isolated.

It remains to consider τ_m<t₀. Assume τ_m is ISOLATED; all four
unique caps now have uniform gaps. If q_m(clock<t₀)>0, reset m
toward its old conditional early law and the other owners toward
their cap atoms. The LEFT retained endpoint of t₀, or the finite
region before c_k if t₀=Never, gives the literal Section 4 transport.
At the selected endpoint both m's displayed response and its
prescribed early clocks are sole-quitter payoffs s_m against later
opponents. The three supported debts are zero. The polynomial is
zero there, contradiction. Hence

    q_m(clock<t₀)=0.                             (12)

If t₀=Never, (12) forces m to prescribe Never surely. The other
three endpoint laws are also Never, while m's displayed response is
finite, so δ=s_m.

For finite t₀ let H={j≠m:τ_j=t₀}, a=q_m(t₀). Resetting just the
three supported owners gives the exact selected endpoint identity

    δ=a[s_m−r_m(H∪{m})]+(1−a)[s_m−r_m(H)].       (13)

If 1−a>0, also reset m toward its OLD conditional law after t₀.
All caps remain fixed by isolation; the constant endpoint yields
δ=s_m−r_m(H) independently. If a>0, resetting m toward its EXISTING
atom t₀ instead yields δ=s_m−r_m(H∪{m}). When no later mass exists,
a=1 and the ORIGINAL m law is pure t₀. Every supported cap later
than t₀ would then tie Never, contrary to uniqueness. Thus all three
supported caps are t₀, H=I∖{m}, and the remaining participant gap is
specifically δ=s_m−r_m(I).

Consequently every isolated strictly-earliest sole-unsupported minimum
has its debt in the finite passive-floor/own-grand spectrum

    F_(i,K)=s_i−r_i(K), K⊆I∖{i}, r_i(∅)=0;
    G_i=s_i−r_i(I).                              (14)

The general participant pair/triple gaps in (13) are NOT substituted
for passive floors; late mass or actual pure play provides the
separate justification. A nonisolated τ_m is NOT consumed by THIS
atom-reset spectrum argument: later opponent resets need not
positively rescale its
previous earlier response. Section 7 supplies the separate global
conditioning exclusion for an all-unique nonisolated earliest cap,
without pretending it has a uniform complement gap.

## 10. Worst SUM selection and finite contact avoidance

For two tables at sup distance e, the SAME actual profile's prescribed
payoff and EVERY response payoff change by at most e. Taking full
suprema changes each cap by at most e. Thus

    |D_r(p)−D_(r′)(p)|≤8e,
    |Δ(r)−Δ(r′)|≤8∥r−r′∥∞.                     (15)

Taking infima in both directions proves the second bound without
fixing a common minimizer. The closed unit cube is compact, so if
any positive gap exists it has an attained positive worst value

    Ω=max_(all unit-cube tables)Δ(r)=Δ(r*)>0.       (16)

Produce a marked minimum of r*. The tracked singleton margin (8)
and B_i≤1 give s_i≤1−Ω. AllNever has D=Σ_i[s_i]⁺. If Ω≥1,
all s_i≤0 and this profile contradicts positivity. Hence Ω<1,
and again using AllNever gives

    Ω≤Σ_i[s_i]⁺≤4(1−Ω), so Ω≤4/5<1.             (17)

This threshold is used to resolve the joint contact target; it is
not an isolated numerical improvement.

### Singleton-preserving signed-eight subtheorem

This is distinct from the expanded construction below. Put
a_i=r*_i(I∖{i})−r*_i(I), χ_i=+1 if a_i≥0 and −1 otherwise.
Change ONLY row i's omitted-triple and grand entries toward
(χ_i,−χ_i), with a common convex parameter α. Then

    |a_i(r^α)|=(1−α)|a_i|+2α.

Let η=min{Ω−|a_i|:|a_i|<Ω}, with η=1 if this set is empty,
and choose α=min(1,Ω,η)/64. The new value lies in
[Ω−16α,Ω] and is positive by (15),(16). Old absolute contacts Ω
move above Ω since Ω<2; old upper values stay above; old lower
values stay below Ω−16α since 18α<η. Therefore

    Δ(r^α)≠a_i(r^α) and Δ(r^α)≠−a_i(r^α) for ALL i.  (18)

Section 6 excludes every LC minimum at this fresh table, regardless
of exceptional-owner switching. All singleton entries, their entire
Γ matrix r_i({j})−r_i({i}), all pairs and all participant triples
are unchanged. Subsequent SUM maximization over the own-singleton
fiber preserves the interval and the no-contact result because it
keeps all a_i fixed; it need not preserve the old own singleton
values or Γ. No MAX-regret source or minimizer transfers follow.

### One expanded target for all source spectra

For the full theorem, discard the preceding subcase table and begin
again with the worst r* of (16). Define a unit-cube endpoint R by

    own singleton: +1;
    passive singleton or passive pair: −1;
    participant pair or participant triple: +1;
    row i omitted triple/grand:
        (0,−1) if a_i(r*)≥0,
        (−1,0) if a_i(r*)<0.

These disjoint cases specify all sixty entries. Use the finite
labelled family V of raw functionals

    a_i                       (4 labels),
    C_A, ∅≠A⊊I              (14 labels),
    J_(i,K), ∅≠K⊆I∖{i}      (28 labels),
    F_(i,K), K⊆I∖{i}        (32 labels),
    G_i                       (4 labels).

There are 82 labels, possibly fewer distinct functionals; repetitions
are harmless. In particular C_(I∖{i})=J_(i,I∖{i})=−a_i. Every
functional is linear in the sixty finite reward coordinates, with
the Never reward fixed at zero.

For EVERY label v with v(r*)=Ω, its target v(R) is at least
one and therefore STRICTLY ABOVE Ω by (17). This is checked by
the complete finite cases:

- a_i=Ω>0 chooses omitted/grand (0,−1), giving target 1;
- C_A targets 6 for |A|=1 and 4 for |A|=2; for |A|=3 it is
  −a_i, whose positive contact chooses (−1,0), giving target 1;
- J_(i,K) targets 2 for |K|=1 or 2; for |K|=3 it is −a_i and
  has the same target 1 at a positive contact;
- F_(i,K) targets 2 for |K|=1 or 2, 1 or 2 for |K|=3, and 1
  for empty K;
- G_i targets 1 or 2.

No individual term is assumed positive inside a C_A contact. The
intermediate zero in each omitted/grand pair resolves the opposing
join and withdrawal requirements. This target CHANGES own singleton
rewards, passive singleton rewards and Γ; it is not the eight-
coordinate, own-preserving direction.

Let σ=min{|v(r*)−Ω|:v(r*)≠Ω}, with σ=1 if all labels are contacts.
It is positive because the labelled family is finite. Choose

    α=min(1,Ω,σ)/64>0, r̂=(1−α)r*+αR.

By (15),(16), its ACTUAL new infimum d satisfies

    0<3Ω/4≤Ω−16α≤d≤Ω.                           (19)

Every functional changes by at most 12α: the longest C_A consists
of three two-entry differences, each entry moving at most 2α;
all other functionals are shorter. For a contact,
v(r̂)=Ω+α[v(R)−Ω]>Ω≥d. For an old upper noncontact,
v(r̂)≥Ω+σ−12α>Ω≥d. For an old lower noncontact,

    v(r̂)≤Ω−σ+12α<Ω−16α≤d,

because 28α<σ. Thus, simultaneously for EVERY label,

    d≠v(r̂).                                      (20)

Old upper values may decrease and old lower values may increase;
finite separation handles both. The proof concerns the entire
possible new value interval and ALL new minimizing laws, not a
fixed active tester or fixed owner's continuation. Worst-table
optimality provides the upper value bound, and all-law Lipschitz
continuity provides the lower bound. Neither can be omitted.

## 11. Fresh-source consumption, overlap and exact nonclaims

Apply Section 3 AFRESH to ANY finite minimizing sequence of the ONE
fixed r̂. Its true debt d>0 avoids every NEW spectrum value by (20).

If all four caps are unique and common, all-supported is excluded by
Section 6. All-zero-own common caps have zero mixture mass and are
excluded by Section 7. A proper nonempty supported set gives forbidden
C_A by Section 8. Thus NOT ALL unique cap dates are equal; pairwise
distinctness is neither inferred nor required.

The earliest supported-group alternative of Section 6 leaves only
LC or an earliest unsupported owner. LC gives forbidden a_m, so
some earliest maximizing owner has zero own point mass. Four supported
unique caps are already excluded, hence some owner is unsupported.

If exactly ONE owner is unsupported, Section 9 excludes its later
case by a_m and its earliest tie by J_(m,H). In the strictly earliest
case Section 7 makes its point a finite positive mixture atom and
therefore isolated. Section 9's F/G spectrum excludes that case too.
Thus an all-unique source has at least TWO unsupported owners. Its
earliest cap is finite and a positive isolated MIXTURE atom by
Section 7, even though some maximizing owner has no own mass there.

This proves the strengthened Section 1 alternatives simultaneously
at EVERY produced minimum. No theorem here consumes the surviving
multiple-cap branch or all-unique sources with two, three or four
zero-own-mass owners at the stated earliest atom. Other recipients
may supply that atom without maximizing there themselves.

The comparison is SUM-aligned from its original no-UE input through
the global table maximum, new value interval and every source
identity. The exact tracked declarations
`exists_maximum_quittingTerminalExploitabilityInf_unitReward` and
`exists_membershipStretch_singletonFiber_source_of_positiveInf` in
`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchWorstTableSource.lean`,
and `exists_membershipStretch_source_opposedReversals_of_no_uniformPayoff_finFour`
in `UniformEquilibrium/Diagnostics/Quitting/MembershipStretchOpposedSource.lean`,
instead optimize MAX debt. Their sign-sensitive membership stretch
and MAX own-fiber selection do not provide (20) for the true SUM
minimum or the all-moving-minimum cap-rank conclusion. The MAX
objective was checked against `quittingTerminalExploitability_eq_max_debt`
in `UniformEquilibrium/Quitting/Terminal/TerminalExploitability.lean`
and `quittingTerminalExploitabilityInf` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean`.
This is a bounded comparison to those relevant source selections,
not a global producer census or a claim of new raw UE-class coverage.

The exact strategic tracked inputs are the unrestricted law/behavior
correspondences and no-UE bridge in Section 2, the original carrier
definition in Section 3, and the singleton-margin theorem (8) under
its actual imports. The marked producer, signed conditional transport,
multiaffine geometry identities and finite contact comparison are
ordinary mathematics proved here; they are not claimed kernel-checked.
No draft/untracked marked-calendar Lean file is an input.

The signed-eight subtheorem preserves the stated singleton data.
The expanded target does NOT preserve singleton normalization,
punishment floors, Γ signs, single-pivot data or a previous strategy's
ancestry. A later own-fiber reoptimization is not asserted to preserve
the expanded contacts, since F and G depend on the own singleton
entries. Reward directions are fixed by the worst table before new
minimizers; active tests born only at a limit are not imported from
old tables. No public mixture or correlated stopping flag is used.

Important boundary checks: δ=0 cannot be substituted for positivity;
at a zero-gap table the finite contact interval need not stay positive.
A positive debt at one profile is not a global floor. Unique caps at
nonisolated points have no automatic uniform gap. Existing supported
Never atoms are legal reset targets, while Never and c remain distinct.
A polynomial all-one endpoint has selected debts, not guaranteed
actual caps. Sole-unsupported original pure play is used in Section 9
only AFTER (12) and absence of late mass force it. Owner changes,
support changes, tied raw contact values, zero and saturated reward
entries, and every original finite deadline are covered by the
simultaneous value comparison and original-chart convergence.

The remaining conjecture-facing question is whether a genuinely
multiple-cap minimum or an all-unique multi-unsupported ATOMIC earliest
minimum admits a global whole-law repair or a further all-table
comparison. The full Fin4 UE theorem remains open.

## 12. Exact boundary tests and allowed law changes

### Zero global gap: unique supported caps do occur

Take r_i(S)=1 if i∈S and 0 otherwise, specifying every finite reward.
Actual all-date-zero Quit gives U_i=B_i=1, debt zero, and each cap
has the UNIQUE supported maximizing point 0. Every later finite
response and Never has payoff zero. This validates that positivity
of the TRUE infimum, not merely cap uniqueness/support, is essential.

In the same table let each owner independently choose half date 0,
half Never. Then U_i=1/2, B_i=1, and D=2. The old positive atom
at 0 permits the legal joint reweighting q_i^λ=(1−λ)q_i+λδ_0.
At λ=1/4 each own date-zero mass is 5/8 and D=4(1−5/8)=3/2.
Small negative λ are legal too. Thus positive debt at one profile
cannot replace a global positive minimum in the sign-cube argument.

### A zero-mixture earliest cap is legal when δ=0

With every reward entry zero, actual all-Never has zero payoff and
debt. Its source has T={c=0}, with c and Never distinct maximizing
points, zero mixture mass at c, and every strict-late mass positive.
Section 7 then only gives the valid zero margin 0≤0, not a contradiction.

### The no-strict-late exception has exact finite witnesses

Set all own singletons zero. Give recipient i≠0 payoff 1 on singleton
{0}, recipient 0 payoff 1 on singleton {1}, and set EVERY other entry
zero. For N≥1 give player 0 the uniform law on {0,…,N−1}, player 1
the uniform law on {N,…,2N−1}, and players 2,3 pure Never. The first
outcome is {0} surely, so exactly

    U=(0,1,1,1), B=(1,1,1,1), D=1.

For i≠0 all finite responses≥N and Never give cap1; before N the
payoff is the chance that 0 has ALREADY stopped, with joint quitting
payoff zero at the last possible early clock. For recipient 0 all
finite responses≥2N and Never give cap1. These are FULL caps.

The limiting old charts have T=[0,1/2], c=1/2, player 0 uniform on
[0,1/4], player 1 uniform on [1/4,1/2], and 2,3 Never. The earliest
active point τ=1/4 is nonisolated and has zero mixture mass. Player0
stops STRICTLY before it surely. Each other recipient has the entire
[τ,c] and Never as maximizing points, exactly Section 7's output.

For cuts u_n↑τ, e_0^n>0 but e_0^n→0. Conditional laws concentrate
into (u_n,τ), with densities growing as 1/e_0^n. Their limit would
insert a new positive atom at an OLD nonisolated point. Bounded
signed old-chart transport DOES NOT authorize that atom. Thus final
strict-late positivity cannot be replaced by positivity at preceding
cuts. The true gap of this table is zero via actual all-Never, so
the displayed D=1 is not substituted for δ.

### Agency and finite realization

All random draws remain playerwise independent. Chart Lebesgue
variables encode marginal laws and are NOT an observed shared signal.
Every finite witness is an actual stopping law or its canonical
behavioral realization. A conditional target changes existing own
mass on an actual chronological event; it does not add a new
nonisolated clock. Supported atoms are moved along their original
retained finite dates. Negative parameters are justified by direct
likelihood positivity. Every full-response comparison includes all
original finite dates, empty dates, arbitrarily late dates, Never,
and the explicit late finite c/c⁺ distinction.

## 13. Narrow Lean handoff and nonclaims

The tracked strategic inputs are ONLY the stopping-law/payoff/full-cap
correspondences and no-UE bridge in Section 2, the actual carrier in
Section 3, and the global singleton margin (8). Their exact declaration
names and source files are given there. No conference file or
untracked marked-calendar implementation is a dependency.

A narrow formalization route is:

1. Produce the old common quantile charts, both E/T limits, bounded
   marginal densities and prescribed/moving-reply AE/L¹ convergence.
2. Transport the specific supported-atom and ordered-conditional
   signed families, retaining nonnegative density bounds and full
   caps. Do not infer negative parameters from forward mixture facts.
3. Prove the upper-family positive affine identity, lower compact
   gap stability and multiaffine interior-minimum principle. The
   simultaneous-cap version in Section 7 needs no unique selector.
4. Prove its actual final conditional full-cap bound (9e), then
   consume the checked singleton margin. Keep selected identity (9c)
   distinct until that bound is established.
5. Formalize the finite source spectra and the SUM reward-infimum
   Lipschitz/compact-maximum/separation comparison. Do not import the
   MAX declarations as a SUM adapter.
6. Combine them into the fresh-table source restriction, preserving
   the ANY sequence / EVERY produced minimum quantifiers.

This is a producer of a STRICTER surviving counterexample class,
not an equilibrium profile or payoff. It does not solve the multiple-
cap branch, assume a child Nash continuation, temporalize response
arrows, preserve singleton normalization under the expanded target,
or infer actual endpoint caps from polynomial constancy. No Lean
build or kernel certification is claimed here.
