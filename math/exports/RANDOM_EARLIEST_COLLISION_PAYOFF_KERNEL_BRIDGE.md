# A fresh positive-gap Fin4 table forces a genuine earliest-to-later payoff-kernel bridge

## 1. Exact theorem and scope

This is an ordinary-mathematical proof, not a Lean-checked theorem.
All needed original finite-law, complete-cap, marked-calendar and
signed-source constructions are proved below. The result is a strict
counterexample-source reduction, not a uniform-equilibrium producer.

Let I={0,1,2,3}. A table assigns r_i(S)∈ℝ to every recipient i
and nonempty coalition S⊆I; all-Never pays0. Strategies are
INDEPENDENT complete stopping laws on ℕ⊔{Never}, equivalently the
original quitting game's unrestricted behavioral strategies. Their
first finite tied coalition determines terminal reward. Caps include
EVERY finite pure response and Never, equivalently ALL unrestricted
behavioral deviations. Put

    D_r(p)=Σ_i[B_i(p)−U_i(p)],
    Δ(r)=inf_(all actual independent law profiles p) D_r(p).

If ANY signed Fin4 quitting game has no uniform-equilibrium payoff,
there exists ONE table r†∈[−1,1]⁶⁰ with Δ(r†)=δ>0 such that:

1. EVERY original closed-carrier minimizing payoff/cap pair has ONE
   COMMON nonnegative debt vector d*. Payoff vectors, caps, laws and
   calendars need not be common.
2. For ANY finite-law minimizing sequence for this fixed table and
   ANY subsequence satisfying the marked producer's convergences,
   EVERY resulting global minimum q has a RANDOM prescribed
   terminal outcome law, not a point mass on any of the sixteen
   coalition/Never labels.
3. Let A_i be its FULL compact set of maximizing responses and
   τ=min(⋃_i A_i). Every prescribed owner has zero probability of
   stopping before τ. The point τ is finite, is an isolated positive
   MIXTURE atom, is the FIRST prescribed stage, and has positive
   OWN atoms for at least TWO owners. It is an actual collision
   stage, not an inferred Nash row.
4. Some owner i maximizes both at τ and at a later compact test σ.
   The TWO full response PAYOFF KERNELS differ on a set of positive
   probability under its ORIGINAL independent opponent laws.
   Their EXPECTED payoffs are nevertheless equal to B_i. This
   distinction has literal original finite moving-response witnesses.

The table is selected BEFORE all final minimizing sequences and
their cap families. The construction avoids at most93 fixed raw
contact values, preserves their typed signs, makes all recipient-row
coalition entries distinct, and THEN selects positive real recipient
scales from a fixed carrier to make every minimizing debt vector
identical. No old minimizing law, singleton normalization, normality,
or MAX-debt selection is transported.

A maximizing root and later clock are necessarily distinct test
points, but Point4 asserts MORE than point multiplicity: it rules out
an earliest active structure consisting only of outcome-equivalent
late/Never aliases. Other active aliases may still exist. The bridge
owner may have ZERO debt. No sign for its pointwise payoff differences,
paid response edge, debtor-rank decrease, root Nash, credible return,
child equilibrium, ordinary strategy-class completeness, or UE
payoff is asserted. A response-complete consumer of this remaining
genuine root-to-later tie is open.

The only strategic tracked inputs are the original behavior/law
and no-UE correspondences in Section2, the original closed carrier
in Section3, and the strict four-player true-minimum margin in
Section6. The table selection, concave recipient scalarization and
all-active signed comparisons are ordinary mathematics proved here.
No untracked declaration or conference file is a proof dependency.

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


## 6. The checked strict margin at a true unweighted Fin4 minimum

Write s_i=r_i({i}). The exact tracked input is
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`,
under its actual imports. Its hypotheses are: a pair in the ORIGINAL
closed attainable carrier; unweighted total debt no larger than
that of EVERY pair in this carrier; exactly four players; M>0;
|r_i(S)|≤M for every finite coalition and recipient; and δ>0.

At such a pair, with d_i=B_i−U_i and Σ_i d_i=δ, it concludes

    B_i−s_i≥δ+δ²/(8M),
    U_i−s_i≥δ−d_i+δ²/(8M)>0 for every i.             (SA2)

The final strict inequality uses 0≤d_i≤δ, already true throughout
the original closed carrier. This is a theorem about the TRUE
unweighted SUM minimum, not a restricted strategy minimum, weighted
minimum at an old table, selected cap, Nash tail or original first-row
Nash condition. Every invocation below occurs at a produced global
minimum of the currently fixed table. For unit-cube tables use M=1.
No singleton sign or same-table punishment premise is needed.

## 7. One sign-adaptive contact-avoiding and row-generic table

For two tables at sup distance e, the SAME actual law profile's
payoff and EVERY response payoff change by at most e. Taking full
suprema changes each cap by at most e. Hence

    |D_r(p)−D_(r′)(p)|≤8e,
    |Δ(r)−Δ(r′)|≤8∥r−r′∥∞.

Take infima in both directions; no common minimizing law is fixed.
The sixty-coordinate closed unit cube is compact, so any positive
gap gives an attained worst value Ω=Δ(r)>0 in that cube. At a
produced true minimum for this OLD worst table, Section6 gives
B_i−s_i≥Ω and B_i≤1, hence s_i≤1−Ω. Actual AllNever debt is
Σ_i[s_i]⁺, so Ω≤Σ_i[s_i]⁺. If Ω≥1, all these positive parts
vanish, contradicting Ω>0. Consequently

    0<Ω≤4(1−Ω), hence Ω≤4/5<1.                      (SA1)

This threshold allows one endpoint to push ALL positive old contacts
above Ω. It is not used as a constants-only improvement.

### SA2. Complete sign-adaptive endpoint and typed mixed-debt labels

For every nonempty K⊆I∖{i}, write

    J_(i,K)=r_i(K∪{i})−r_i(K),
    a_i=r_i(I∖{i})−r_i(I).

Construct ONE endpoint R from the OLD worst table r:

- R_i({i})=1 for all four own singletons.
- For EACH lower pair of coordinates (r_i(K),r_i(K∪{i})), with
  |K|=1 or2, if OLD J_(i,K)>0 assign (−1,1); otherwise assign
  (0,−1/2). Thus the endpoint join is2 or−1/2 respectively.
- For each omitted-triple/grand pair, if OLD a_i≥0 assign
  (R_i(I∖{i}),R_i(I))=(0,−1); otherwise assign (−1,0).

This specifies all sixty coordinates without overlap: 4 own singletons,
12 passive singleton/participant pair pairs, 12 passive pair/participant
triple pairs and 4 omitted-triple/grand pairs. All targets lie in the
unit cube. OLD ZERO lower joins belong to the negative target branch;
OLD ZERO grand withdrawals belong to the positive branch. Those
choices are essential for the following EXACT fresh sign census.

For a coalition A of size2,3 or4 put

    W_(i,A)=r_i(A∖{i})−r_i(A), i∈A,
    J_(z,A)=r_z(A∪{z})−r_z(A), z∉A.

Define from OLD r the future-positive cohorts

    E_A={i∈A: W_(i,A)(r)≥0},
    Z_A={z∉A: J_(z,A)(r)>0},
    V_A=Σ_(i∈E_A)W_(i,A)+Σ_(z∈Z_A)J_(z,A).          (SA3)

For a triple's omitted owner, J_(z,A)=−a_z; hence its membership
in Z_A is OLD a_z<0. For the grand coalition E_I={i:a_i≥0}
and Z_I=∅. Include V_A in the labelled family ONLY if

    |E_A|≥2 OR |Z_A|≥1.                              (SA4)

There are at most eleven added labels. Include the following82 canonical labels:
four a_i; fourteen C_H=Σ_(i∉H)J_(i,H), ∅≠H⊊I;
twenty-eight individual J_(i,H), ∅≠H⊆I∖{i};
thirty-two F_(i,K)=s_i−r_i(K), K⊆I∖{i}, with r_i(∅)=0;
and four G_i=s_i−r_i(I). Labels may coincide numerically or be
negative; they are not replaced by a selected positive witness.
The combined family ℱ has at most93 labels and coefficient absolute
sum at most8. This is the finite family used below, not a claim
of additional coverage merely from the contact count.

For ANY positive convex step r^α=(1−α)r+αR, 0<α<1,
all twenty-four lower joins and all four a_i are nonzero, with

    J_(i,K)(r^α)>0 ⇔ J_(i,K)(r)>0,
    a_i(r^α)>0 ⇔ a_i(r)≥0.                          (SA5)

Consequently the positive member withdrawals and outsider joins for
EVERY A are EXACTLY E_A and Z_A. The weak old inequalities in E_A
allow NEW positive branches born from OLD zeros. This statement is
about table signs, not limiting maximizing tests or an old law.
Positive recipient scaling preserves all these signs exactly.

### SA3. Every old positive contact is pushed above Ω

For every labelled v∈ℱ with v(r)=Ω, one has v(R)≥1>Ω.
Here is the complete check over the full label set:

- a_i=Ω>0 selects the endpoint a_i=1.
- A singleton-set C_H is a sum of THREE lower joins. A positive
  old sum has at least one old positive term. Its endpoint is at
  least2−1/2−1/2=1, even with two negative or zero old terms.
- A pair-set C_H is a sum of TWO lower joins. Its endpoint is at
  least2−1/2=3/2 for a positive old sum.
- A triple-set C_H=−a_i. Positive old contact requires a_i<0,
  whose negative endpoint is1.
- A positive individual lower join has endpoint2; a positive
  triple individual join is−a_i and has endpoint1.
- Each F has endpoint1 or2: own singleton1 minus passive
  singleton/pair0 or−1, omitted triple0 or−1, or Never0.
- Each G has endpoint1 or2 since the grand endpoint is0 or−1.
- For the included mixed labels, literal endpoint values are

      |A|=2:  |E_A|/2+2|Z_A|,
      |A|=3:  |E_A|/2+|Z_A|,
      |A|=4:  |E_A|.

  Under (SA4) each is at least1. In particular TWO indebted
  triple members already target1; no assumption that EVERY
  member withdraws or that an outsider blocks is imposed.

This is why the negative joins are not simply given target−2.
Such a target would destroy the positive C_H direction. Conversely,
assigning every participant payoff1 and passive payoff−1 would drive
pure pair/triple withdrawal sums NEGATIVE and could not price them.
The negative magnitude−1/2 accommodates BOTH the join and mixed-debt
contacts. No claim is made that arbitrary independent-law debt is one
of these finite values; Section9 proves precisely the class for which it is.

### SA4. Global finite comparison with ALL moving minimizers

Let σ be the minimum positive |v(r)−Ω| over labels not equal to Ω,
using σ=1 if that set is empty. Put

    α=min(1,Ω,σ)/64,       r^α=(1−α)r+αR,
    d=Δ(r^α).

Both reward tables lie in the unit cube and their distance is at most
2α. Worst-table maximality and the actual debt-infimum modulus give

    Ω−16α≤d≤Ω,       d≥3Ω/4>0.                     (SA6)

An old contact v(r)=Ω has v(r^α)=(1−α)Ω+αv(R)>Ω≥d.
An old upper noncontact is at least Ω+σ−16α>Ω≥d.
An old lower noncontact is at most Ω−σ+16α<Ω−16α≤d,
because 32α<σ. Thus EVERY v∈ℱ differs from the actual NEW gap.
All statements allow every new minimizing profile and every moving
response tester. We have not transported any old minimizing law.


### SA5. Make rows generic while preserving every contact gap and typed signs

The convex-step table r^α already has δ₀=Δ(r^α)>0, every label in
ℱ avoids δ₀, and every lower join and grand withdrawal is strictly
nonzero with the EXACT future-positive cohorts E_A,Z_A of (SA5).
Let γ be its minimum contact gap and κ its minimum magnitude among
those nonzero joins and withdrawals.

Contract all rewards by a common positive factor arbitrarily close
to1. This puts EVERY entry strictly inside the unit cube. The true
SUM infimum and every homogeneous raw label scale by the SAME
factor, so positivity, all contact gaps and all typed signs persist.
Denote the contracted quantities by δ₁,γ₁,κ₁.

Choose a small sup-norm perturbation radius β, contained in the open
unit cube, satisfying

    8β<δ₁, 16β<γ₁, 2β<κ₁.

Avoid the finite collection of hyperplanes r_i(S)=r_i(S′) for
distinct nonempty S,S′ in each row; their complement is dense.
Choose a table r̂ within this ball. The all-law gap changes by at
most8β, every contact by at most8β and every join/withdrawal by
at most2β. Therefore δ̂=Δ(r̂)>0, all labels avoid δ̂, all typed
positive cohorts remain EXACTLY E_A,Z_A, and

    r̂_i(S)≠r̂_i(S′) for all i and distinct nonempty S,S′.       (SA7)

This is a table selection BEFORE any final minimizing law. Positive
recipient scaling next preserves all within-row inequalities and
typed signs. Its size is chosen also to preserve every one of the
at most93 contact gaps. No generic perturbation is made AFTER a
debt-rigidity selection.

## 8. Fixed-carrier recipient scales make every minimizing debt vector identical

### DR2. The genuinely concave scale objective

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

    Δ(r̂^θ)=W(θ),
    min_i θ_i ·δ̂≤W(θ)≤max_i θ_i ·δ̂.              (DR1)

Here δ̂=Δ(r̂)>0. The lower bound uses nonnegative debts at ALL actual profiles and
extends to the closure. The upper bound evaluates an old true SUM
minimum. Therefore every positive θ retains a positive gap. Positive
row scaling is strategically equivalent for exact Nash and, after
rescaling accuracy, for uniform-payoff existence; it does not manufacture
a different deviation probability mode.

### DR3. A producer of ONE debt vector for EVERY minimizing pair

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

### DR4. Preserve all finite exclusions before selecting new laws

Let ζ=min_v |v(r̂)−δ̂| over all labels in ℱ; ζ>0.
Every label has coefficient absolute sum at most8. If ∥r′−r̂∥∞<ρ,
then |v(r′)−v(r̂)|≤8ρ, while |Δ(r′)−δ̂|≤8ρ by the whole-law
reward modulus. Choose 0<ρ<min(1/2,ζ/32). Then

    |v(r′)−Δ(r′)|≥ζ−16ρ>0 for EVERY label.        (DR4)

Choose a coordinate-regular θ from DR3 inside (1−ρ,1)⁴, possible
because the exceptional set has measure zero. Set r†_i(S)=θ_i r̂_i(S); it
is within ρ of r̂, remains in the unit cube, and has positive true
unweighted gap δ=W(θ). Equations (DR1),(DR4) preserve ALL
contact exclusions. Positive row scales preserve (SA5)'s exact
typed cohorts and (SA7)'s distinct row entries. ALL global minima
of THIS fixed final table have the ONE vector d* from (DR3).

No maximization of W or SUM after this selection is required; no
old debt vector is identified with a new one. No final minimizing
law or calendar was selected during any of these table steps.

## 9. Every final prescribed terminal outcome is random

### SA6. Deterministic outcomes give exact raw debts and a literal repair

Work at ANY produced ORIGINAL-carrier positive global minimum with
(SA2). Suppose the
prescribed outcome is deterministic. If it is Never, every law is
Never, U_i=0, and (SA2) forces every s_i<0; all caps are0, contradicting
δ>0. If it is a singleton {h}, absorption there gives U_h=s_h,
also contradicting (SA2), even with a diffuse sole-owner clock.

Let the deterministic coalition A have |A|≥2. Independence implies
all its members are PURE at ONE common finite time t_A. Indeed any
two member clocks are independent and equal almost surely; their
bounded COLLAPSED clock coordinates, not the raw Lebesgue draws,
then have covariance0 and equal variance, so variance0. Every
outsider is strictly later than t_A almost surely.
Therefore U_i=r_i(A) for every player. For a member i, responding at
t_A yields r_i(A), and responding later or Never yields r_i(A∖{i}).
For an outsider z, joining at t_A yields r_z(A∪{z}), while every
later or Never response yields r_z(A). Earlier finite responses,
when available, yield s_i. The cap-minus-singleton margin in (SA2)
excludes this earlier value as a maximizer. Thus the ACTUAL debts are

    d_i=[W_(i,A)]⁺, i∈A,
    d_z=[J_(z,A)]⁺, z∉A.                            (SA8)

This is also exactly the semantic pair of the LITERAL date-zero
pure-A profile with all outsiders Never. Its only response values
are the displayed root and wait rewards; dropping the old earlier
solo tests changes no cap because they were strictly below B_i.
This is a legitimate nonlocal SAME-table profile replacement, not
a convex mixture of minimizing pairs or an unsupported old-chart
atom reset. In particular the date-zero pure-A profile is itself
an actual global minimum if the hypothetical marked one was.

Assume all W_(j,A), j∈A, and J_(z,A), z∉A, are nonzero and that
EXACTLY ONE member i has positive debt, with no indebted outsider.
Then W_(i,A)=δ>0, every other member has W_(j,A)<0, and every
outsider has J_(z,A)<0. Use the literal date-zero profile and change
ONLY member i to quit at0 with probability1−ρ and Never with
probabilityρ. Every other A member remains sure at0; outsiders
remain Never. This is an actual independent behavioral law.

Owner i's cap is independent of its own law and equals r_i(A∖{i}).
Its prescribed payoff improves by ρδ, so its debt is (1−ρ)δ.
For another member j the root payoff is

    P_j(ρ)=(1−ρ)r_j(A)+ρr_j(A∖{i}).

Every later/ Never response at ρ=0 pays r_j(A∖{j}), strictly less
than r_j(A). Changing i's law perturbs EVERY response uniformly by
at most2ρM and its root payoff by at most2ρM. This includes the
pair case: on i's Never branch the other member can choose any
finite deadline or Never, but that branch has probabilityρ and
bounded reward, so no new large cap is hidden there. Taking
4ρM<min_(j∈A∖{i})(−W_(j,A)) keeps root j's full cap at its
prescribed P_j(ρ); its debt stays0. An empty minimum is ignored.

Every outsider still faces at least one retained sure member at0.
ALL later and Never tests equal its prescribed passive payoff
(1−ρ)r_z(A)+ρr_z(A∖{i}). Its root join was strictly lower atρ=0,
and remains so when 4ρM<min_(z∉A)(−J_(z,A)). Thus its full debt
stays0 as well. There are no earlier-than-zero finite tests.

Choose ρ>0 satisfying these finitely many strict bounds. The exact
WHOLE-law debt is

    D=(1−ρ)δ<δ,                                    (SA9)

contradicting global minimality. No punishment tail or selected child
Nash is used. This repair works even though the changed Never atom
was unsupported in the old source; it is performed in a literal
original-calendar profile whose complete pair was already equal
to the source pair. It is not authorized as a negative density reset.

### SA7. Consumption of ALL deterministic prescribed outcomes

At the final table, signs (SA5) make EVERY W and J in (SA8) nonzero.
The positive branches are EXACTLY E_A and Z_A selected at OLD r.
If |E_A|≥2 or |Z_A|≥1 then actual δ=V_A(r†), contradicting
Section8's preserved no-contact gap for that included label.
If both cohorts are empty, actual debt0 contradicts δ>0.
The only remaining possibility is |E_A|=1 and Z_A=∅, which SA6's
actual one-law release strictly improves. Singleton and Never
were separately excluded there. Therefore EVERY final-table
minimum has a random prescribed outcome. With finitely many
outcome labels, at least TWO labels have positive probability.

This includes atomic earliest paid outsider joins: it is not merely
the pure unhappy coalition whose all members strictly withdraw.
It does not exclude an outcome law supported on {A,Never}, a random
pair/triple distribution, or any source solely because its cap set
has several points. There is no linear outcome-mixture repair.

## 10. No pre-active head; the first prescribed stage is an active collision

### SA8. ALL-active signed head box, including accumulating cap sets

Let q be ANY freshly produced final-table marked minimum, with full
compact response sets A_i and τ=min(⋃_i A_i), allowing Never.
Choose finite regular ORDERED cuts u<a<τ with q_j(clock=u)=0
for all j. These are cuts in the collapsed chronological clock order,
not raw quantile coordinates. The event clock≤u includes each retained
date WHOLE; its raw π-preimage boundary is the RIGHT endpoint after
its last included atom, which need not equal u. In an isolated-point
clock gap this raw prefix boundary can stay fixed as u varies.
Put B={i:e_i=q_i(clock≤u)>0}.
If B is nonempty, for each i∈B use the OLD conditional head
ν_i=q_i(·|clock≤u) and independent signed parameters

    q_i^λ=(1−λ_i)q_i+λ_iν_i.

The head/late density factors are 1+λ_i(1/e_i−1) and 1−λ_i.
They are positive and bounded on a common small two-sided box.
An e_i=1 direction is redundant; no new clock is introduced.

This is realized on the ORIGINAL finite minimizing sequence using
chronological conditionals at whole old atom intervals. Their raw cut
boundaries converge to the π-preimage prefix boundary just specified,
not to a cut through an interval midpoint. Their indicators converge
in L¹, and their positive masses tend to e_i. The literal
old density is multiplied by

    (1−λ_i)+(λ_i/e_i^k)1_(clock≤u_k).

Its common bound and the strong indicator convergence give the
required weak-* density convergence. All old retained collapse
maps and moving finite-test kernels stay unchanged. The marked
product/kernel convergence proves prescribed payoff AND full cap
convergence for every fixed parameter vector: every original
maximizing deadline has an old-chart subsequential tester, and each
fixed limit tester has original approximants. Never stays separate
from finite c, and c⁺ remains an exact duplicate because the
targets add no mass at c. Hence EVERY small signed family pair
belongs to the ORIGINAL closed carrier and has actual D≥δ.

For EVERY response t>a and every player i, expand the opponents'
independent product. A term containing any head replacement exits
by u<t, so its payoff is independent of t, including t=Never.
Consequently

    V_i(t,q_-i^λ)=k_i(λ)V_i(t,q_-i)+C_i(λ),
    k_i(λ)=Π_(j∈B∖{i})(1−λ_j)>0, t>a.              (SA10)

The constant C_i is the SAME for ALL upper testers, not a selected
branch derivative. The compact lower tester set≤a contains NO old
maximizer and has a strict uniform gap. Product coupling bounds
all response changes by2M times the sum of opponent total-variation
changes. On a small signed box the lower gap stays strict, and
(SA10) preserves EXACTLY all upper orderings and all active ties.
Thus the ENTIRE old A_i remains the full maximizing set, even
when it has accumulating or outcome-equivalent points.

Choose any representative σ_i∈A_i and form

    F_i(λ)=V_i(σ_i,q_-i^λ)−U_i(q^λ).

The sum F is multiaffine, equals actual D on the signed box, and
has an interior GLOBAL minimum δ at0. Averaging over a small
centered cube, or inspecting the first nonzero squarefree part,
forces F≡δ algebraically. Every point on the small box is a TRUE
original minimum; final-table debt rigidity therefore gives
F_i=d*_i there. Each individual multiaffine polynomial is consequently
IDENTICALLY d*_i, also at its algebraic all-head endpoint. No claim
that the distant endpoint retains old full caps follows from this
polynomial identity; only the small signed box is cap-stable.

### SA9. Strict pre-active mass collapses to a deterministic coalition

Let P={i:q_i(clock<τ)>0}. Any such owner has d*_i>0: its
nonnegative regret integrand B_i−V_i(t) is strictly positive at
every pre-active clock and is integrated on a positive-mass set.

For a regular cut with B={h}, the own response cap B_h is unchanged
by the sole-law modification. Constancy of F_h says the prescribed
payoff is unchanged as h is conditioned to its old head. All
opponents are later than u, so that conditional payoff is s_h.
Thus the ORIGINAL U_h=s_h, contradicting the tracked strict
prescribed margin (SA2). This consumes the sole-head case without
assuming that another debtor, sure-owner punishment, or child Nash
has been produced.

For |B|≥2, fix i∈B and set every other B owner algebraically to
its head. Both i's own late conditional branch and its chosen
response σ_i≥τ>u are screened by another sure head≤u, so they
have identical passive payoff. Decomposing i's original law gives

    F_i(own old law, others heads)
      =e_i F_i(all heads).

Both polynomials equal d*_i; its positivity gives e_i=1 in the
ORIGINAL q_i. This conclusion holds for every i∈B. For j∉B,
its own law and σ_j are later than u, screened by sure heads at
the all-head endpoint. Its selected polynomial is0 there, so
d*_j=0. Thus no j∉B can have positive pre-active mass: B=P.

If P is nonempty, choose the smallest essential support endpoint
t₀ of its mixture. If t₀ is isolated in the retained clock set,
use ONE ordered cut u in its right clock gap and below τ. Its
whole-atom raw prefix ends at the RIGHT endpoint of t₀'s retained
interval; there is some positive head, and the preceding paragraph
gives B=P and q_i(clock≤u)=1 for every i∈P. By minimality of
t₀ and the clock gap, all those laws are pure at t₀. If t₀ is
nonisolated, it has zero mixture atom; use decreasing regular ORDERED
cuts u_n↓t₀ below τ, each with some positive head present. For
EACH n, singleton B is impossible and the preceding paragraph gives
B=P, |P|≥2 and q_i(clock≤u_n)=1 for every i∈P. Again EVERY
P owner is PURE at ONE finite t₀<τ in the ORIGINAL source.
Every outsider stops≥τ>t₀. Its prescribed terminal outcome is
therefore deterministically P, contradicting SA7.

The legal boxes, density bounds and lower gaps may depend on the
fixed cut; no uniform bound as u_n↓t₀ is assumed or needed. Each
individual cutoff identity already concerns the ORIGINAL q.

Hence for EVERY produced minimum,

    q_i(clock<τ)=0 for ALL i.                        (SA11)

This proof allows randomly absorbing coalitions initially and makes
no within-row distinct-payoff, unique active test or isolated active
set assumption. The deterministic conclusion is derived ONLY in
the hypothetical pre-active branch by actual signed transport and
all-minimum debt rigidity, then consumed by SA7.

### SA10. The first prescribed stage is finite, active and a collision

If τ=Never, (SA11) makes every law Never and its full debt0 once
Never is earliest active: all finite own-singleton rewards are≤0.
This contradicts δ>0. Thus τ is finite. If its mixture atom had
mass0, all opponents would stop strictly later than τ, and an
owner maximizing at τ would have B_i=V_i(τ)=s_i. This contradicts
the cap margin (SA2). Therefore τ has positive mixture mass and
is isolated by the retained positive-atom chart construction.
Equation (SA11) says it is exactly the FIRST prescribed stage.

Suppose just one owner h has positive root atom a=q_h({τ}).
If a=1 then U_h=s_h, contradicting (SA2). If 0<a<1, take the
literal ORIGINAL finite suffix after the retained τ cut, conditioned
on continuation by each owner, and reindex its unchanged integer
calendar. The h continuation mass tends to1−a>0; the other masses
tend to1. Compactness supplies an actual suffix carrier pair (u,b)
with D_tail=Σ_i(b_i−u_i)≥δ. Vanishing pre-root absorption and
vanishing other root rates give the exact limiting ledger

    U_h=a s_h+(1−a)u_h,    B_h=max(s_h,b_h),
    U_j=a r_j({h})+(1−a)u_j,
    B_j≥a r_j({h})+(1−a)b_j, j≠h.

This uses ALL suffix deadlines/Never and the original conditional
sequence; it does NOT assert that the suffix minimizes debt or
is Nash. The h margin implies b_h=B_h>s_h. Therefore

    δ≥(1−a)D_tail+a(B_h−s_h)
      ≥(1−a)δ+a(δ+δ²/8)>δ,

contradiction. At least TWO owners thus have positive atoms atτ.
The first root has genuine nonsingleton probability, not a new
Never floor or a purely continuous collision-free strategy class.
It may have sure owners and may still have several random coalition
outcomes or cap kernels. These residuals are not consumed here.

## 11. An earliest-to-later active bridge is unavoidable and has different payoff kernels

### BG3. If no cap bridges the root, the complete root box is stable

Fix ANY final produced minimum. Sections9–10 show that it is
nondeterministic, has no prescribed pre-root mass, and has at least
two root suppliers. Suppose it has NO owner maximizing both
at τ and at a later compact point. Let

    R={j:a_j=q_j({τ})>0}.

R is nonempty. Every owner whose cap contains τ has cap set EXACTLY
{τ}. This is not an assumption that the other owners' caps are
unique: they may have arbitrary compact later maximizing sets,
including equivalent finite/Never plateaus.

For j∈R independently use the existing supported-atom reset

    q_j^λ=(1−λ_j)q_j+λ_jδ_τ.

The original retained positive interval supplies actual finite
targets at its retained date n_k. Its own atom mass tends to a_j>0,
so small parameters of BOTH signs are legal. The old-chart density

    (1−λ_j)f_j^k+λ_j 1_(J_k)/|J_k|

is uniformly bounded and nonnegative; interval indicators converge
in L¹, yielding weak-* convergence, product/payoff convergence and
ALL moving-cap convergence. Unit mass gives a redundant direction,
not an illicit negative probability. Never stays separate and c⁺
duplicates c exactly; no new mass is inserted at a nonisolated point.

A root-only cap has the isolated compact complement gap. For an
owner with ALL its active points later, compactness and isolation
of τ permit one cut a>τ strictly below its entire active set; when
the only active point is Never choose τ<a<c. Each product term
containing a reset opponent quits at τ, before EVERY response t>a.
Consequently on the WHOLE upper family,

    V_i(t,q_-i^λ)=k_i(λ)V_i(t,q_-i)+C_i(λ),
    k_i=∏_(j∈R,j≠i)(1−λ_j)>0.

This preserves ALL maximizing equalities and upper orderings, not
just one selector. The compact lower set contains no active point
and remains below the upper maximum locally. Thus EVERY full cap
stays represented by its original active set on one signed box,
even if every later cap set is multiple and nonisolated.

Select any original maximizer σ_i for each owner. The selected
summed-regret polynomial is the ACTUAL debt throughout this box.
It is multiaffine, has interior global minimum δ, and hence is
constant. Every box pair is a true original-carrier minimum. ALL-
minimum rigidity now makes EACH individual polynomial identically
d_i, algebraically at distant parameter endpoints too. Those far
evaluations remain SELECTED regrets, not actual endpoint cap claims.

### BG4. This forces a deterministic original root cohort

Section10 already proves |R|≥2. Consider each ORIGINAL root supplier;
no new pure root profile is assumed.

Consider any h∈R. If its cap is root-only, its own reset toward
its maximizing root has

    d_h(q^λ)=(1−λ_h)d_h(q)

on the actual box. Rigidity forces d_h=0. The ONLY maximizing
point is τ, so zero expected regret implies the ORIGINAL q_h
is pure at τ. This is actual original purity, not a polynomial
endpoint inference.

If all its cap points are later, its positive prescribed atom at
the strictly suboptimal root gives d_h>0. In the polynomial identity
condition all OTHER members of R to the root. There is another
sure root owner. With h on its old conditional late law (>τ),
both its prescribed clock and any selected σ_h>τ are screened
by the same other-owner root coalition, so the raw regret is zero.
With h conditioned to the root, its selected regret is d_h by
individual polynomial constancy. Leaving h original gives

    d_h=a_h d_h+(1−a_h)·0,

forcing a_h=1. If a_h=1 already, no late conditional is defined
or needed. Again this is ORIGINAL purity. All outside-R laws are
strictly after τ by Section10 and their zero root masses.

Every member of R is therefore originally pure at τ, and every
other owner is later. The actual prescribed terminal coalition is
deterministically R, contradicting nondeterminism. This proves that
EVERY final produced minimum MUST have a root-to-later bridge,
not merely some pair of abstract maximizing point labels.

### BG5. The bridge really distinguishes payoff kernels

Choose the bridging owner i and any later active σ. The root
response is its full cap, so the strict margin (SA2) gives

    V_i(τ)=B_i≥s_i+δ>s_i.

If no opponent had positive root mass, its response at τ would
be its own singleton s_i, impossible. Thus with positive probability
at least one opponent exits at τ. On that event let S≠∅ be the
opponents' tied root coalition. Because there are no earlier draws,
the response at τ gives coalition S∪{i}, while the response at
ANY σ>τ, including Never, gives coalition S. These are different
coalitions on a set of positive probability. At least one such
nonempty S has positive event probability, since there are finitely
many possible S.

The fresh row genericity gives

    r_i(S∪{i})≠r_i(S).

Thus the two FULL response payoff kernels differ on that positive
probability set of the ORIGINAL opponent laws. This is not merely
a c/Never alias behind a sure old owner. Equality of their expectations
is the genuine active tie that remains to be priced. No claim about
a sign of the pointwise differences, a positive debt of i, or a
root Nash condition is made.

This distinction has literal finite witnesses as well. Retain the
original root date n_k and one original moving response σ_k for σ
(or literal Never). Since τ is isolated and σ>τ, σ_k>n_k eventually.
For a nonempty root coalition S with positive limiting opponent
probability, the event that EXACTLY its members stop at n_k and
all other opponents are later has probability tending to that
positive value. Root masses and through-root masses converge by
the retained interval's endpoint density tests. On this event the
two actual finite responses give respectively S∪{i} and S. The
SAME fixed generic reward difference is nonzero for every k. No
new nonisolated insertion or asymptotic tester alias supplies the
kernel distinction.

These finite test values converge to the common source cap B_i.
Exact co-maximality of the two responses at EACH finite k is not
asserted; the actual positive-event kernel distinction is exact.


## 12. Exact boundary tests and failed stronger implications

### Positive global debt cannot be replaced by positive profile debt

Take r_i(S)=1 if i∈S and0 otherwise, specifying all60 entries.
All owners pure date0 gives U_i=B_i=1, genuine global debt0,
and each cap has the UNIQUE supported maximizing point0. Every
later finite response and Never pays0. Thus supported unique caps
are legal at zero true gap.

Instead give every owner half date0/half Never. Then U_i=1/2,
B_i=1 and D=2. Its prescribed terminal outcome is random and all
caps are root-only. The legal old-atom change
q_i^λ=(1−λ)q_i+λδ_0 gives at λ=1/4 date0 mass5/8 and
D=4(1−5/8)=3/2. Both parameter signs near0 are legal. This exact
nonminimum cannot replace δ in any interior-minimum argument.

With every reward entry0, all-Never gives U=B=0 and its marked
calendar can have T={c=0}, with finite c and Never distinct
maximizing points. No positive-minimum contradiction follows.
Never and c/c⁺ are not identified with each other.

### The sign-adaptive endpoint needs both kinds of contacts

Set all own singletons0, passive singleton/pair rewards0,
participant pairs−1/4 except r_1({0,1})=1, participant triples−1/6,
and omitted-triple/grand rewards0. These instructions give all60
entries in the unit cube. AllNever has debt0, so the true gap is0.
The coefficient level1/2 below is NOT substituted for a minimum.

Here C_{ {0} }=1−1/4−1/4=1/2. Each of the five pairs other
than {0,1} has two positive member withdrawals summing1/2.
Every triple has three positive member withdrawals summing1/2
and outsider join0. Under Section7's target these values become
respectively1,1,3/2. The pair {0,1} has one positive member
withdrawal and no positive outsider join, so its mixed label is
omitted and its entire class belongs to the literal release
consumer. The grand label is old0 and targets4. All target
coordinates are assigned and lie in the unit cube.

Giving every old negative join target−2 would instead make
C_{ {0} } target−2. Giving all lower joins positive target2
would make the eligible member-withdrawal labels negative. Neither
failed target can replace the sign-adaptive one. These are exact
coefficient tests, not positive-gap examples or optimization traps.

### Debt rigidity is not pair rigidity or independent profile mixing

Coordinate regularity is essential: the abstract compact nonnegative
debt set A={e₀,e₁,e₂,e₃} has W(θ)=min_i θ_i. At θ=(1,1,1,1)
its four minimizing vectors differ and coordinate derivatives fail;
off the tie walls one debt vector is common. This is a convex-
analysis boundary test, NOT a realized positive-gap quitting table.

For a literal two-player table with both own singletons1, both
passive singleton rewards2, and joint reward0, pure date0
singleton profiles have payoff/cap pairs
((1,2),(1,2)) and ((2,1),(2,1)). Both are true debt0 minima.
Independent half-date0/half-Never mixing gives U_i=3/4;
date0 response1/2, Never1 and EVERY later finite response3/2.
The full SUM debt is3/2, not0. This embeds completely in Fin4:
for recipients0,1 let rewards depend on S∩{0,1}, paying0 for
empty projection and the listed rewards otherwise; recipients2,3
pay0 for all coalitions and prescribe Never.

Thus one common debt vector at all minima does not imply common
payoffs/caps, or authorize a correlated or independent mixture
of different minimizing laws. Similarly, individual polynomial
constancy does not follow just from a constant sum:
F₀(u)=1+u,F₁(u)=1−u have constant sum2 on a small positive
box and changing coordinates. Section11 gets individual identities
only AFTER actual full-cap stability and ALL-minimum rigidity.

### Different tests and coalitions are not automatically different payoff kernels

Set r_i(S)=1 for ALL finite coalitions and recipients. Let owner0
be pure date0 and each other owner half date0/half Never. The
prescribed coalition is random and U_i=B_i=1, with global debt0.
For j≠0, date0 and Never are both maximizing. Their coalition
kernels differ because one joins owner0 and the other does not,
but their payoff kernels are identically1 against these opponents.
Section7's row genericity is what rules out this equality on the
positive root event, not merely the use of two distinct clocks.

The bridge owner is not asserted to have positive debt. The
following complete unit-cube table makes that distinction exact.
Own singletons are1, all passive singleton/pair rewards are−1,
all participant pair/triple rewards are1; rows0,1,2 have
(omitted-triple,grand)=(0,−1), row3 has(−1,0). These rules
specify all60 entries.

Let0,1,2 quit surely at date0 and3 quit there with probability q,
otherwise Never. The exact unrestricted full debt is

    D(q)=1−q+3[3q−2]⁺.

For each core owner, root payoff is1−2q, every later finite/
Never payoff is−1+q, and its prescribed payoff is the root one.
Owner3 has root cap0, wait payoff−1 and debt1−q. The root-rate
family has minimum1/3 at q=2/3. All THREE genuine root-to-later
bridges then have ZERO debt; the only debtor3 has a ROOT-ONLY
cap. Core payoff kernels differ on the two opponent-root events
by2 and−1, although their expected values tie.

This is NOT a positive-gap example or a positive global minimum.
Elsewhere the literal pure coalition{0,1,3} has payoff/cap pair
((1,1,0,1),(1,1,0,1)), so the true Δ is0. It also disproves
using a positive restricted root-family minimum or priced pure
endpoints as a substitute for the FULL global source. No argument
here upgrades a genuine kernel tie to a paid response drain.

### All probability modes and actual clocks remain literal

Chart Lebesgue variables parameterize separate marginal laws and
are NOT a publicly observed shared random signal. Every conditioned
target changes only existing mass on a chronological event and
has a direct legal negative-parameter likelihood. An isolated
atomic clock uses its WHOLE original retained date; a nonisolated
cut has zero boundary mass. The proof never inserts a new atom
at a nonisolated clock, assumes a Nash old tail, or assumes a
conditioned tail minimizes debt.

Each moving response includes original empty dates, arbitrary late
finite dates and Never. The c⁺ finite duplicate remains exact
only because these old-law changes keep zero mass at c; uniqueness
and bridges always refer to actual compact TEST POINTS, not that
duplicate representation. Far polynomial endpoints carry selected
regrets, not automatic actual cap or minimizing-profile claims.

## 13. Narrow formalization handoff and the unconsumed branch

The exact strategic declarations and files are given in Sections2,3,6.
The carrier is the ORIGINAL closure of attainable behavioral pairs;
all finite-law approximation estimates are proved in Section3,
uniformly over unrestricted deviations. No supplied Nash root,
punishment plan, sparse outcome law or local security interface
is an unproduced strategic input.

A narrow route is:

1. Construct the old quantile charts, endpoint/test-set Hausdorff
   limits, bounded marginal weak-* limits and prescribed plus ALL
   moving-response AE/L¹ kernel convergence.
2. Transport existing positive atoms and chronological conditional
   laws for BOTH parameter signs, preserving nonnegative bounded
   densities and actual complete cap convergence.
3. Prove the whole-upper-family positive affine identity, compact
   lower gap stability and multiaffine interior-minimum principle.
   Apply it to FULL active families, not a favorable test selector.
4. Formalize the true SUM table modulus and compact worst table,
   complete60-coordinate endpoint, typed93 signs/labels and finite
   separation. Make rows generic BEFORE the debt-rigidity selection.
5. On the fixed original carrier, prove the concave positive-scale
   objective, coordinate-regular real-weight producer and ONE debt
   vector for EVERY final unweighted SUM-minimizing pair.
6. Establish deterministic pair equality with a literal date0
   profile, then the one-sided actual release with uniform ALL-
   deadline/Never caps, including a pair's newly exposed singleton.
7. Combine true-minimum rigidity with the signed pre-active head box,
   retaining whole-date/right-boundary cuts, to remove all heads.
   Extract the ACTUAL original conditional suffix for the sole-root
   supplier inequality; it is not assumed Nash or minimizing.
8. Stabilize all root-only/later full caps together on the signed
   root box, derive ORIGINAL purity from individual polynomial
   identities, and obtain the genuine bridge by random-outcome
   contradiction. Keep endpoint selected regret separate from full
   cap claims.
9. Retain the positive root-coalition event and its original moving
   finite witnesses for the payoff-kernel distinction.

All these new production/comparison steps are ordinary mathematics,
not asserted Lean declarations. The nearby tracked weighted
singleton margin
`minimumTerminalSemantic_weightedSingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticWeightedAuxiliaryNashBudget.lean`
takes an ALREADY supplied positive weighted minimum and positive
weights; it does not produce coordinate-regular weights or one
debt vector for ALL minima. No fixed-current-minimizer Danskin
rule in reward space is used here.

The exact MAX-based sources
`exists_maximum_quittingTerminalExploitabilityInf_unitReward` and
`exists_membershipStretch_singletonFiber_source_of_positiveInf` in
`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchWorstTableSource.lean`,
and
`exists_membershipStretch_source_opposedReversals_of_no_uniformPayoff_finFour`
in
`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchOpposedSource.lean`
optimize MAX debt rather than this unweighted SUM. They are not
adapters for the present moving-minimum value interval or the
generic93 fixed-table comparison. This is a narrow nearby source
distinction, not a global classification census.

The full conjecture remains OPEN. The final residual is an actual
FIRST active collision with RANDOM terminal outcome and a genuine
earliest-to-later PAYOFF-kernel bridge at a debt-rigid minimum.
The root may have sure owners, the bridge owner may have ZERO
debt, other maximizing points may be equivalent plateaus, and the
conditional old tails need not be Nash or minimizing. No paid edge,
return, rank drop, ordinary-class coverage or uniform payoff has
been inferred. A legal finite-amplitude global repair must control
ALL changed full caps rather than select one active branch.
