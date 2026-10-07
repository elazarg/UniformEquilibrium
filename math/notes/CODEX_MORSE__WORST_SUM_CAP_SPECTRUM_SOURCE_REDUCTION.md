# Worst-SUM reward selection reduces the surviving Fin4 cap geometry

## 1. Exact theorem and status

This is a complete ordinary-mathematical proof candidate, not a
Lean-checked result. The compact-source producer and its required
signed transport are proved below. No unidentified strategic source,
Nash continuation, or minimizing conditioned tail is an input.

Let I={0,1,2,3}. A reward table assigns r_i(S)∈ℝ to every owner i
and nonempty coalition S⊆I; all-Never has reward zero. A profile
consists of four INDEPENDENT complete stopping laws on ℕ⊔{Never}.
If a finite first stopping date occurs, the coalition of players
stopping at that date determines the terminal reward. Pure responses
include EVERY finite date and Never. All behavioral replacements,
not a bounded controller or prescribed response menu, are permitted.

For prescribed payoff U_i, complete response payoff V_i(t,p_-i), and
complete cap B_i=sup_t V_i(t,p_-i), put

    D_r(p)=Σ_i[B_i(p)−U_i(p)],
    Δ(r)=inf_(all actual independent stopping laws p) D_r(p).

If ANY signed Fin4 game has no uniform-equilibrium payoff, there is
another table r̂ with all sixty entries in [−1,1] and Δ(r̂)=d>0
having the following property. Apply the explicit marked producer
in Section 3 to ANY finite-law minimizing sequence for r̂, and take
ANY subsequence satisfying its stated convergences. At every resulting
marked global minimum q:

1. The four complete caps cannot all have the same UNIQUE maximizing
   point.
2. If all four complete caps have unique maximizing points τ_i, some
   EARLIEST maximizing owner has zero own point mass at that point.
3. If all four caps are unique and exactly one owner m has zero own
   point mass at its cap, τ_m is STRICTLY EARLIER than the other three
   caps and is NONISOLATED in the marked finite-test calendar.

Thus every such minimum has either a multiple-maximizing-point cap,
or distinct unique cap dates with at least two unsupported owners,
or a sole unsupported owner whose maximizing point is strictly earliest
and nonisolated. “Unsupported” in this packet means ZERO OWN POINT
MASS, not exclusion from topological support. A nonisolated point has
zero mixture point mass, but isolation alone need not imply positive
mixture mass.

The table is selected ONCE before ANY new minimizing sequence or its
owner/support geometry is selected. No old minimizing law is carried
through a reward change. This is an existential counterexample-class
reduction, not a restriction on every original counterexample table,
an equilibrium producer, or closure of the full Fin4 conjecture.

There is also a distinct eight-coordinate subtheorem in Section 10:
one can preserve ALL singleton rewards and exclude every exceptional-
latest unique-cap configuration. The stronger theorem above changes
own singleton rewards and must not inherit that preservation claim.

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

## 7. Common unique caps with zero mixture mass are impossible

Suppose all four unique caps are the same τ and q_i(τ)=0 for all i.
It is finite: if τ=Never then all laws are finite a.s., and c and
Never have identical response payoffs, contradicting uniqueness.
Every e_i=q_i(clock>τ) is positive. Otherwise owner i stops strictly
before τ surely and every other τ cap ties Never.

The checked declaration `minimumTerminalSemantic_singletonMargin`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
states, for membership in the ORIGINAL semantic carrier, a positive
GLOBAL SUM minimum, and every owner,

    δ≤B_i−s_i, s_i=r_i({i}).                      (8)

No tail Nash, reward sign or punishment hypothesis occurs. If τ were
the first finite calendar point, all opponents have zero mass there
and V_i(τ)=s_i, contradicting (8). We may therefore take ordered
cuts u_n<τ increasing to τ. At an isolated zero-mass point any
sufficiently close lower cut gives the same conditional law; otherwise
use the approaching cuts. Set ν_i^n=q_i(·|clock>u_n). Their positive
normalizers tend to e_i>0, and ν_i^n→ν_i=q_i(·|clock>τ) in total
variation because the mixture atom at τ is zero.

For each fixed n, signed resetting ALL laws toward ν_i^n has expansion
(5) with early support ≤u_n. For all responses t>u_n, their payoff
ordering is positively rescaled exactly as in (4). The compact lower
set excludes τ and has a strict gap. Hence all displayed caps remain
τ on a small signed box. Section 4 supplies literal finite witnesses
for these ordered conditionals, including zero-mass boundary cuts.
The constant polynomial endpoint and then n→∞ give

    δ=Σ_i[V_i(τ,ν_-i)−U_i(ν)]
      =Σ_i[s_i−U_i(ν)],                          (9)

since all opponents under ν stop strictly after τ. This is initially
only a selected-response identity.

To obtain ACTUAL complete caps, write ν_j=(q_j−E_j)/e_j where
E_j=q_j|_(clock<τ). There is no atom at τ. In the opponent expansion,
every term containing an E_j has exited strictly before every t≥τ,
including τ, c and Never. Thus for all t≥τ,

    V_i(t,ν_-i)=k_i V_i(t,q_-i)+C_i,
    k_i=∏_(j≠i)e_j⁻¹>0,

with the SAME C_i at τ. Old maximality implies V_i(t,ν_-i)≤s_i.
For finite t<τ, all opponents are later and the payoff is also s_i.
Therefore the complete cap of ν is exactly s_i, over ALL tests;
c⁺ still duplicates c. Section 4 realizes this nonsigned final ν
in the original carrier. Equations (9) and the global floor show its
ACTUAL sum debt is δ, so it is a true global minimum. Apply (8) there:
δ≤B_i(ν)−s_i=0, contradiction. No selected endpoint is silently
declared a minimum; its actual full cap bound is what supplies that
step.

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
separate justification. A nonisolated τ_m is NOT consumed: later
opponent resets need not positively rescale its earlier response,
and uniqueness there does not give a uniform complement gap.

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
fixed r̂. Its debt is d>0 and avoids every NEW spectrum value by (20).

If all caps are unique and common, all-supported is excluded by
Section 6, all-zero-own by Section 7, and the proper supported set
gives the forbidden C_A by Section 8. Thus unique caps cannot all
be common. The earliest-group alternative of Section 6 has only
LC or an earliest unsupported owner; LC gives forbidden a_m, so
there is an earliest unsupported owner. If exactly one owner is
unsupported, Section 9 excludes its later case by a_m, its earliest
tie by J_(m,H), and its strictly-earliest isolated case by F or G.
It must be strictly earliest and nonisolated. This proves all three
claims in Section 1 simultaneously at EVERY produced minimum.

Every positive produced finite mixture atom is isolated and Never
is isolated, so that remaining nonisolated cap has zero mixture
point mass and is finite. It can still belong to topological support.
No theorem here consumes multiple maximizing points or sources with
two, three or four unsupported owners at distinct cap dates.

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

The remaining conjecture-facing question is whether the nonisolated
earliest observer cap, or a genuinely multi-unsupported/multiple-cap
minimum, admits a GLOBAL whole-law repair or another whole-table
comparison. The full Fin4 UE theorem remains open.
