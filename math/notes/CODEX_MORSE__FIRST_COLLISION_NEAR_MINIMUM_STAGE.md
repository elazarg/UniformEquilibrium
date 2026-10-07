# Positive global minima force an early original collision stage

## 1. Exact original-profile theorem

Let I be a finite player set of cardinality n≥2. For every nonempty
coalition S⊆I fix a real reward vector r(S). At the first natural-number
date with one or more Quit actions the game absorbs at that coalition;
perpetual Continue has terminal reward zero. Private randomization is
independent. Before absorption the only public history is all Continue,
so each unrestricted behavioral strategy has an independent stopping law
on ℕ∪{Never}. A deviator may replace its COMPLETE law. No public
correlation, finite-memory restriction or selected response is assumed.

Let U_i(p) be prescribed terminal payoff, b_i(p) the supremum over every
unilateral behavioral deviation, and

    D(p)=Σ_i[b_i(p)−U_i(p)],       δ=inf_p D(p).

Equivalently the cap is over ALL pure finite stopping dates and Never.
Assume δ>0 and either

    n=4, with arbitrary signed rewards; or
    n is any finite cardinality ≥2 and r_i({i})≥0 for every i.

Choose M>0 bounding every reward entry in absolute value, and define

    κ=δ/(4M),   γ=δ²/(8M),   A=κ/n,
    h₀=Aγ/[8M(n+1)],   σ=A h₀/(n−1),   N=2^n−n−1.

**Theorem.** For every ζ>0 there is ε>0 such that EVERY actual independent
stopping-law profile p satisfies

    D(p)≤δ+ε
      ⇒ ∃t∈ℕ ∃S⊆I with |S|≥2:
           P_p(absorption strictly before t)≤ζ,
           P_p(first coalition S at date t)≥σ/(2N).       (A)

The original first-coalition STAGE probability is exactly

    m_S(t;p)=∏_{i∈S}p_i({t})
                ·∏_{j∉S}p_j({t+1,t+2,…,Never}).

No law or calendar in conclusion (A) is modified. The profile may have
infinitely many finite dates; all its complete behavioral caps enter D.
The stage floor depends on the fixed table's δ and M, but NOT on ζ.
The required near-minimum tolerance may depend on ζ. No bound on t,
lower Never mass, or exact pair coalition is asserted. For Fin4 the
stage floor is σ/22.

A same-sequence statement gives the geometric content. From ANY specified
finite-law minimizing sequence one can extract a marked ordered limit
and ORIGINAL dates t_k such that

    P(absorption strictly before t_k)→0,
    liminf m_S(t_k;p^k)≥σ/N

for one fixed nonsingleton S, without changing any original profile.
The limiting calendar has a FIRST positive atom, of total marginal
mass greater than κ, and at least two players have positive mass there.
This first row is not asserted to be a Nash row.

These are necessary original-source restrictions on every positive global
terminal gap, not a proof of uniform-equilibrium existence or a positive-gap
example. They exclude diffuse minima, solo-first minima, and all near-minimum
families lacking a uniformly large early ORIGINAL collision stage. All
strategic data used in the proof are produced from the given minimizing
sequence. The proof below retains its entire payoff/cap limit and traces
the final stage back to that same sequence.

## 2. The marked-calendar minimum and its complete variation domain

### Statement and exact scope

Fix a finite nonempty player set I of cardinality n and an arbitrary real
reward vector r(S) for each nonempty S⊆I. Fix M>0 bounding every absolute
reward. All players' stopping laws are independent; all Never pays zero.
For an actual finite stopping-law profile p on ℕ∪{Never}, write U_i(p)
for prescribed terminal payoff and b_i(p) for the supremum over EVERY
pure finite stopping date and Never. This is the unrestricted behavioral
cap, since before absorption the only live public history is all Continue
and each behavioral strategy has one independent stopping law. Define

    D(p)=Σ_i[b_i(p)−U_i(p)],
    D_*=inf{D(p): p is an actual independent finite-law profile}.

The same infimum results from allowing arbitrary stopping laws. Indeed,
move each law's finite mass after K to Never. Those moved masses tend to
zero, and coupling bounds each prescribed payoff and every unilateral
payoff test uniformly by 2M times the relevant changed masses. Taking
suprema proves convergence of every complete cap and of D.

**Unregularized representation theorem.** There exist a nonempty compact
ordered set T⊆[0,1], c=max T, a separate Never point after T, and independent
probability laws q_i on T∪{Never}, with q_i({c})=0 for all i, such that

    D_T(q)=D_* .                                  (1)

Here quitting at t∈T has its literal earliest-coalition meaning, including
ties, and b_i^T(q) is the supremum over ALL t∈T and Never. Each such cap
is attained. More strongly, from any specified actual finite minimizing
sequence one can extract a subsequence having all its first-coalition
probabilities, prescribed payoffs and complete caps
converging to those of q, including the joint-Never probability.

The represented minimum has the following produced variational domain.
Adjoin one empty finite test c⁺>c, distinct from Never, and put T⁺=T∪{c⁺}.
For ANY finitely supported probability laws ν_i on T∪{Never} and ANY
λ_i∈[0,1], define independently

    q_i'=(1−λ_i)q_i+λ_iν_i.

There are actual independent finite profiles whose coalition laws,
payoffs and unrestricted caps converge to those of q' with ALL tests
in T⁺ and Never. Consequently

    D_{T⁺}(q')≥D_*=D_T(q).                        (2)

The choices of ν_i and λ_i can be simultaneous and need not agree across
players. There is no supplied equilibrium, cap selector or payoff witness.
The conclusion does not assert that q is a law on ℕ, that every compact-
calendar variation is legal, or that one family of approximating profiles
simultaneously realizes every counterfactual replacement. The finite
approximation in (2) may depend on the complete chosen variation.

### Weak-* likelihoods and the marked calendar

Start with ANY specified actual finite sequence p^k with D(p^k)→D_*.
All subsequences below are taken from that same sequence. Put
μ^k=Σ_i p_i^k/n. Give each date, followed by Never, an interval in [0,1]
of length μ^k at that date. Intervals with zero length are omitted. On
the interval of a date a define

    r_i^k(x)=p_i^k(a)/μ^k(a).

These deterministic coordinate charts do not introduce a shared random
draw: the players still sample their coordinates independently. They give

    0≤r_i^k≤n,   Σ_i r_i^k=n almost everywhere,   ∫r_i^k=1.

Since L¹[0,1] is separable, the bounded ball of L∞ is weak-* sequentially
compact. Passing to a common subsequence for finitely many players gives

    r_i^k ⇀* r_i,   0≤r_i≤n,   Σ_i r_i=n a.e.,   ∫r_i=1.             (3)

Let c_k=1−μ^k(Never) and pass to a subsequence with c_k→c. Let E_k contain
the endpoints of all the atom intervals, together with 0,c_k,1. For every
actual finite response date t define its location

    x_k(t)=μ^k({a:a<t})+μ^k(t)/2,

and let T_k be the finite set of these locations. A supported finite date
is represented by its atom midpoint; an empty date by the cumulative mass
strictly before it. Every date after the last finite support has location
c_k. Never is NOT such a date: it remains a separate tester label.

Hausdorff compactness of the nonempty compact subsets of [0,1] gives a
further common subsequence E_k→E and T_k→T. Thus 0,c,1∈E, T⊆[0,c]
and c∈T. No endpoint lies in the interior of the limiting Never interval
(c,1). For each component J=(a,b) of [0,c] outside E there is exactly
one original atom interval J_k=(a_k,b_k) approaching J. An interior compact
subinterval of J eventually contains no endpoint and hence lies in one
atom; Hausdorff convergence forces that atom's endpoints to a and b.
Moreover

    T∩J={(a+b)/2}.                               (4)

Only the atom midpoint is an actual test in its interior, and that midpoint
is always available. The weak-* limit r_i is constant almost everywhere
on J. To see this without strong convergence, take any two compact
subintervals inside J: r_i^k is the same constant on both for large k.
Weak-* convergence of their integrals identifies the same limiting
constant. Exhaust J by compact subintervals. The identical argument shows
constancy on (c,1) when this interval is nonempty.

The part of E outside T is null. In fact, each component of the complement
of T has at most one point of E, apart from the harmless endpoints outside
[0,c]. Two distinct such endpoints would force an original atom midpoint
between nearby approximating endpoints, contradicting the positive distance
from T. There are only countably many complement components.

Define π almost everywhere on [0,1]: collapse each J to its midpoint,
leave the remaining points of E∩[0,c] in place, and send (c,1) to Never.
Its values belong to T∪{Never} outside a null set. Define q_i=π_*(r_i dx),
using independent draws. Since c is an endpoint, not an atom midpoint,
q_i({c})=0. Its mixture is π_*dx, so the only positive finite atoms are
the retained component midpoints. All other finite points are non-atomic.

### Why weak convergence is sufficient for all semantic coordinates

The required product statement is stronger than convergence against
continuous functions but follows directly from (3). The product
densities R^k(x)=∏_i r_i^k(x_i) converge weak-* in L∞([0,1]^n) to
R(x)=∏_i r_i(x_i). For a rectangle test ∏_i 1_{A_i}(x_i) this is the
product of the marginal weak-* identities. Finite linear combinations
of rectangle indicators are dense in L¹ of the product cube, while
0≤R^k,R≤n^n. Approximation proves the claim for EVERY fixed L¹ test.
The same argument applies to each opponent product with n−1 factors.

Let π_k be the original interval-collapse map, with Never separate.
For each coalition S, including the all-Never outcome, let K_S^k be
the corresponding first-coalition indicator on the product cube. Then

    K_S^k→K_S almost everywhere and in L¹.        (5)

Exclude the countably many endpoints of components of [0,c] outside E,
the point c, and equality of any two independent Lebesgue coordinates.
Two remaining finite draws either lie in one component J, hence eventually
in the same original atom J_k, or have a limiting endpoint strictly between
them, which eventually separates their original atoms. Their order cannot
reverse. Never membership stabilizes as well. This proves (5), including
all simultaneous quitting coalitions, not just singleton outcomes.

Now split the integral difference into

    ∫K_S^k R^k−∫K_S R
       =∫(K_S^k−K_S)R^k+∫K_S(R^k−R).           (6)

The first term is bounded by n^n‖K_S^k−K_S‖₁ and tends to zero; the second
uses the FIXED-kernel weak-* limit. Thus no unjustified product of two
weak limits is present. This proves coalition-law and payoff convergence.

For complete caps, take ANY sequence x_k∈T_k with x_k→x∈T. If x is a
retained midpoint, (4) forces x_k eventually to be the corresponding
midpoint and retains its exact tie. Otherwise x∈E and the limiting
prescribed law has no mass at x. A retained atom adjacent to x stays on
its correct side: its midpoint is separated from the endpoint x. All
remaining order comparisons stabilize off a null set. Consequently the
opponent payoff kernels for this moving response converge almost everywhere
and in L¹. The opponent version of (6) proves convergence of the actual
pure-response payoff. Never is treated separately by its first-coalition
kernel. This argument applies also to x_k=c_k, so the last finite response
is never confused with Never, even for negative own singleton rewards.

The limiting pure-response payoff is continuous on T. A retained midpoint
is isolated by its half-atom length. At all other points, the same cut
argument with the fixed limit laws proves continuity. Never is an isolated
label. Hence the limiting cap is attained. Choose finite maximizers and
extract convergent locations to obtain limsup b_i(p^k)≤b_i^T(q). Approximate
a limiting maximizer by T_k using Hausdorff convergence to obtain the
reverse liminf inequality. Therefore all full caps converge. Equation
(1) follows from D(p^k)→D_*.

### Transport of simultaneous finite-atomic variations

Here is the complete response-location issue in (2). Let Z be the union
of the finite supports of the ν_i, excluding Never. If z∈Z is a retained
positive atom, put the inserted masses at its corresponding original
date. That atom's full probability vector converges by weak-* convergence
on its interior and bounded density near the moving endpoints.

If z has zero prescribed mixture mass, choose disjoint shrinking
neighborhoods of these finitely many z. Shrink them slowly enough to
dominate the Hausdorff errors and to make their original mixture masses
tend to zero. This is possible because the original mixture at quantile
locations converges weakly to π_*dx and the latter has no atom at z.
Consolidate the consecutive original-calendar block in each neighborhood
to one date by a COMMON monotone quotient, before adding any mass.
This removes the otherwise spurious multiplicity of collapsing empty dates.
At c include the last finite support and the first empty date after it
in the block, but retain a later empty date for c⁺. If the original finite
support is empty, use date 0 and its following date. Rename the resulting
finite ordered calendar consecutively; this is a literal natural calendar.

On this common calendar use the independently mixed laws prescribed in
(2), with Never unchanged as a label. The mixture flags are independent
across players. Conditional on each choice of flags and inserted atoms,
the remaining base factors satisfy (3)–(6). The probability that any
base draw belongs to one of the shrinking consolidated blocks tends to
zero. This proves every prescribed coalition-law limit; inserted ties
at one chosen common date are preserved exactly.

For the upper cap bound take any sequence of modified finite pure tests.
Away from Z the preceding moving-test argument applies. At z∈Z distinguish
before, coincident and after. Coincident is the pure-z test. A strictly
before limit can survive consolidation only if T has points approaching
z from below; otherwise Hausdorff convergence puts all nearby original
tests inside the one block. When such approach exists, its limiting payoff
is bounded by the supremum over those ACTUAL T-tests. The right-hand case
is identical at interior z. At c the after value is exactly the extra c⁺
test. Never is separate. This exhausts all maximizing sequences and gives
the upper cap inequality, without assuming a limiting maximum for q'.

For the lower bound approximate each fixed point of T outside Z by
original dates outside the shrinking blocks. Each point of Z has its
chosen date, c⁺ has its later empty date, and Never is unchanged. Their
payoffs converge by the same finite-flag argument. Taking the supremum
gives the opposite cap inequality. Every approximating profile is actual
and finite, so has D≥D_*; taking the limit proves (2).

This proof transports one COMPLETE simultaneous variation at a time.
It does not supply joint realization of an arbitrary counterfactual table
at a single finite index, or identify the represented calendar with ℕ.

## 3. Original semantic source and strict minimum margins

Let M>0 bound all absolute reward entries. Every prescribed payoff and
complete cap lies in [−M,M], and each cap is at least the prescribed
payoff by using the prescribed own strategy as a deviation.

The terminal semantic carrier is the closure of actual payoff/cap pairs
(U(p),b(p)) in finite-dimensional space. The exact definitions inspected
are `quittingTerminalSemanticPair` and `quittingTerminalSemanticCarrier`
in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
Finite censoring in Section 2 shows that its minimum sum debt is precisely
δ. The represented pair lies in that carrier by its joint convergence
of both coordinates. Every transported variation is also in the carrier.

The needed existing source theorem is
`minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.
Its mathematical statement in this notation is:

    if (U,b) is a global carrier SUM-debt minimum of value δ>0,
    then δ≤b_i−s_i for every i, where s_i=r_i({i}).       (C)

This is not an all-player debt-tie assertion for a maximum-debt minimum.
In particular, δ≤2M. The argument below uses (C) both at the initial
actual minimum and at every subsequently established actual minimum.

No-UE supplies δ>0 on the original table. More precisely, the inspected
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` identifies
failure of a uniform-equilibrium payoff with a positive uniform terminal
exploitability gap over ALL behavioral profiles. Maximum debt≤D≤n times
maximum debt. Conversely δ=0 supplies terminal approximate equilibria
for every accuracy, and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
gives one fixed original-game uniform-equilibrium payoff. Thus (A) is a
necessary original-table restriction on every no-UE game in the stated
cardinality/own-level scope, without a
normalization or a supplied strategy witness.

The finite-support approximation declaration inspected is
`exists_finiteDeadlineTimingProfile_approximation` in
`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`.
The elementary uniform-cap coupling in Section 2 proves the exact
sum-debt approximation needed here without silently substituting a
maximum-debt objective.


The stronger source declarations used here are
`positive_minimum_nonnegativeOwner_quadraticMargins` and
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
The former assumes the selected owner's nonnegative own singleton; the
latter assumes cardinality four and has no own-sign hypothesis. Both
assume original carrier membership, GLOBAL sum-debt minimality, positive
debt, M>0, and the absolute bound on every original reward. They internally
produce the necessary strict preemptor; no blocker or strategic witness is
supplied as an extra premise. Under either scope of the main theorem,
every owner at EVERY actual minimum therefore satisfies

    b_i−s_i≥δ+γ,
    U_i−s_i≥δ−(b_i−U_i)+γ≥γ,   γ=δ²/(8M)>0.      (7)

The last inequality follows because nonnegative individual debts sum
to δ. These bounds concern the original table and SUM-debt minimum.
They require no additive normalization of a represented law. The proof
below applies them only after both carrier membership and global
minimality have been established. Their source presence does not by
itself formalize the marked-calendar or chronological conclusions.

## 4. All-retained-cut erasure with exact cap transport

Let q,T,c be the represented source of Section 2 and let δ=D_*>0.
Its prescribed-payoff/cap pair is in the original terminal-semantic carrier,
because one actual sequence converges to both coordinates. It minimizes
sum debt there by continuity. The inspected declaration
`minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
therefore gives, for every i,

    b_i(q)−s_i≥δ,       s_i=r_i({i}).             (8)

This is a SUM-debt statement. No all-player debt tie from a maximum-debt
minimum is imported. In particular δ≤2M.

Choose ANY available finite cut a∈T, including a positive atom. Put
x_i=q_i({t∈T:t<a}) and suppose

    Σ_i x_i≤δ/(4M).                              (9)

Each x_i<1. Let q_i^+ be q_i conditioned on t≥a, including Never.
The claim is

    D_{T∩[a,c]}(q^+)=δ.                          (10)

The suffix cap includes the ACTUAL tied test a and Never. It does not
include an invented empty response before a. When a is nonatomic it
already pays s_i. At an atomic a, deletion of earlier empty testers will
instead be justified by the actual endpoint's strict singleton margin.

For x_i>0 let q_i^- be the conditional prefix law. Hold these two laws fixed
and let z_i be their mixture mass, forming

    q_i^z=z_i q_i^-+(1−z_i)q_i^+.

Coordinates with x_i=0 stay fixed at z_i=0. These are actual admissible
represented-law variations, although they are not merely an application
of the finite-atomic formula (2). Here is their separate transport.
Use the finite realizing sequence from Section 2. If a is nonatomic,
choose original available tester locations tending to a and split strictly
before those actual dates. Their atom lengths tend to zero; the prefix
probabilities x_i^k converge to x_i. If a is a positive atom, use its UNIQUE
original marked date a_k and split strictly before that date. In the latent
quantile chart the cut is the atom interval's LEFT endpoint, not its
midpoint. Endpoint convergence again gives x_i^k→x_i and leaves the
entire original tied row in the suffix.
For x_i>0, reweight each finite prefix and suffix by z_i/x_i^k and
(1−z_i)/(1−x_i^k), respectively. These are exactly normalized probability
laws. Zero-prefix coordinates are left unchanged. The factors converge
to z_i/x_i and (1−z_i)/(1−x_i) and are bounded for fixed z, while the
prefix indicator converges almost everywhere
in the common quantile chart. The product weak-* and moving-kernel proof
(3)–(6) therefore applies to these reweighted laws. No dates are inserted
or deleted: all old tests remain available, even where their new prescribed
mass is zero. Complete caps and prescribed payoffs converge. Hence

    D_T(q^z)≥δ                                   (11)

for every such z∈[0,1]^J, where J={i:x_i>0}. In particular this is not an
orbit-minimum hypothesis or a conditional-law selection assumed without proof.

For a response strictly before a, no opponent stops before or together with
the responder except on an event of probability at most Σ_{j≠i}z_j. Therefore
its payoff is at most

    s_i+2MΣ_{j≠i}z_j.                            (12)

The cap over responses at or after a, including Never, has the exact form

    L_i(z)=A_i(z₋ᵢ)+[∏_{j≠i}(1−z_j)] b_i(q^+).

Here A_i is the expected passive payoff from the first opponent prefix
coalition; it is multiaffine in z₋ᵢ. The prescribed U_i(q^z) is multiaffine
in all coordinates. Consequently

    P(z)=Σ_i[L_i(z)−U_i(q^z)]

is a multiaffine polynomial. At z=x, (8), (9) and (12) give a strict
gap of at least δ/2 between every early response and its full cap. The same
gap remains positive in a neighborhood of x. Thus D_T(q^z)=P(z) there.
By (11), x is a local minimum of P, interior in all coordinates J.

A multiaffine polynomial with an interior local minimum is constant.
For completeness take a small axis-aligned cube about that minimum.
The center value is the average of its corner values. Every corner is
at least the local minimum, so all corner values equal it. Multiaffine
interpolation makes the polynomial constant on that cube, and polynomial
identity then makes it constant everywhere. Thus P(z)≡δ on the face J.

Now follow z(t)=(1−t)x, 0≤t≤1. Let C be the set of t for which
D_T(q^{z(t)})=δ. It is nonempty and closed, since every cap along this
finite-dimensional mixture family is uniformly Lipschitz in z. At a point
of C the represented pair again belongs to the original carrier and is
a global sum-debt minimum. Therefore (8) applies to that point too.
Meanwhile (12) and Σz(t)≤Σx bound every early response by s_i+δ/2.
No early response can attain its cap. This is a uniform strict gap, so
nearby t still has D=P=δ. Hence C is also relatively open. Connectedness
gives C=[0,1]. At t=1 there is no prefix mass, so every old prefix
test pays exactly s_i. The actual endpoint is a global minimum, and (8)
gives its full cap at least s_i+δ. Hence the entire full cap is attained
in the retained suffix; no old prefix tester is binding. Those empty
tests can be deleted without changing any payoff or cap. This proves (10)
even when a is atomic and no empty pre-atom response is available.

For completeness the deletion also has ACTUAL finite realizers. At z=0,
positive-limit head coordinates have no finite prefix mass. If a coordinate
had zero limiting head mass, remove its vanishing finite prefix mass and
renormalize its suffix; this changes every payoff and cap by o(1), uniformly
in all tests. The full finite prefixes are now empty and their responses
pay exactly s_i. Their suffix caps converge to values at least s_i+δ,
so eventually those caps exceed s_i+δ/2. Deleting the empty earlier dates
and shifting the first retained original date to integer date zero
preserves all complete caps exactly at those indices. The resulting
whole actual profiles converge to the suffix pair, whose debt is δ.
No new pre-tie response has been introduced.

The preservation uses all cap tests, not a chosen cap witness. It also
uses global minimality twice: first to make the multiaffine branch locally
minimal, then to prevent a new early cap from binding during continuation
to z=0. A mere inequality for the derivative at one point would not justify
the continuation step.

The result erases only a head of total marginal mass at most δ/(4M).
It makes no claim about a larger head or conditioning on zero survival.
At the cut it preserves the entire original simultaneous row, not just
a tagged coalition or one selected cap witness. The next section consumes
this actual return using the strict margin (7).

## 5. No small positive head and a large first chronological atom

Put κ=δ/(4M)≤1/2. For an available cut a∈T, put
x_i=q_i({t<a}) and H(a)=Σ_i x_i.
Suppose 0<H(a)≤κ. Section 4, including its atomic-cut source proof,
makes the actual conditional suffix q^+ another GLOBAL minimum of debt δ.
Let u_i and B_i be its prescribed values and complete suffix caps.
For J={i:x_i>0}, retain each original conditional head law q_i^- and
form independent head/tail mixtures with head probabilities z_i. On the
J-face the polynomial

    P(z)=Σ_i[L_i(z)−U_i(q^z)]

is identically δ. The L_i are the complete POST-CUT response envelopes,
not an assertion that every cap is post-cut at every z. Constancy follows
from actual global minimality and the strict head-response gap at the
original interior point, exactly as in Section 4.

Choose i∈J and evaluate this POLYNOMIAL with only z_i=z nonzero.
All other players use q^+. Whenever i selects its head it quits ALONE
strictly before every opponent. Its exact polynomial terms are

    L_i=B_i,       U_i=z s_i+(1−z)u_i;
    L_j=z r_j({i})+(1−z)B_j,
    U_j=z r_j({i})+(1−z)u_j       for j≠i.

Consequently

    P(z e_i)=(1−z)δ+z(B_i−s_i)
             =δ+z[(B_i−s_i)−δ].                   (13)

Constancy gives B_i−s_i=δ. But the returned suffix is an ACTUAL minimum,
so (7) gives B_i−s_i≥δ+γ. Contradiction. Thus

    H(a)=0 or H(a)>κ for EVERY a∈T.                (14)

This uses polynomial evaluation, not an unjustified identification of
P with actual debt at the one-head vertex. Actual source membership and
all caps are needed only at the original local minimum and the returned
all-tail vertex. At an atomic cut, deletion of the earlier empty testers
is valid because the endpoint's true cap exceeds s_i by at least δ.
The tied row at a is retained and no pre-atom tester is inserted.

### The first atom is in the original minimum

The function H:T→[0,n] is continuous on T. At nonatomic points this is
ordinary continuity of cumulative mass; at every positive represented
atom, the point is isolated in T. There is no mass at c. The aggregate
finite mass H(c) is positive: otherwise q is all Never, impossible at
a positive actual minimum, since its cap is max(s_i,0) and the strict
cap margin (7) cannot hold (and all nonpositive owns give debt zero).
By (14), H(c)>κ.

The two nonempty subsets

    Z={t∈T:H(t)=0},       F={t∈T:H(t)>κ}

are closed in compact T and cover T. Closedness of F follows from the
missing interval (0,κ]. Let a=max Z and a^+=min F. Monotonicity gives
a<a^+, and no retained test lies strictly between them. Since every
finite law is supported on T,

    q_i({t<a})=0 for every i,
    w=Σ_i q_i({a})=H(a^+)−H(a)>κ.                 (15)

Thus a is the FIRST positive chronological atom of the ORIGINAL minimum,
not the output of an iterated conditioning procedure. All earlier tests
are genuinely empty and pay s_i. They are strictly inactive by (7),
so deleting only those empty tests preserves the exact whole semantic
pair. The first row has probabilities p_i=q_i({a}), with total hazard
greater than κ. Some probabilities may equal one; no Never floor has
entered this argument.

The compact separation argument handles Cantor-like or disconnected T
without inventing a cut inside a gap. The positive jump is the mass at
the actual retained left endpoint a. In particular all fully diffuse
represented minima are excluded, whatever their zero-Never pattern.

## 6. Exact solo-row ledger and exclusion

Here is the full ledger and the required actual tail source. Suppose
exactly one first-row hazard is positive, p_i=p∈(0,1). Let q^+ be the
independent conditional tail strictly AFTER the first atom. Its prescribed
values are u_j, its complete caps B_j, and its debts d_j=B_j−u_j, with
d=Σ_j d_j. The normalizers are 1−p for i and 1 for every other player.

The original first atom is isolated in T. Its unique marked finite date
and the next remaining original tester delimit the suffix. Restrict
each original finite marginal to the dates strictly after that atom
and normalize. Both the normalizers and moving response kernels converge;
all future finite tests and Never are retained. Thus q^+'s payoff/cap
pair belongs to the original carrier and d≥δ. There is no inserted empty
pre-tail response and no conditioning on a null event.

For i the initial Quit value is s_i, complete Continue value is B_i,
and prescribed value is p s_i+(1−p)u_i. Its cap max(s_i,B_i) exceeds s_i
by the original minimum margin, so that cap is B_i. For j≠i put

    Q_j=p r_j({i,j})+(1−p)s_j,
    C_j=p r_j({i})+(1−p)B_j.

Its prescribed value is p r_j({i})+(1−p)u_j and its complete cap is
max(Q_j,C_j). Subtracting and summing, INCLUDING all branch ties, yields
the exact solo Bellman identity

    D_solo=(1−p)d+p(B_i−s_i)+Σ_{j≠i}[Q_j−C_j]⁺.

The same identity holds for any such solo-first-row profile whenever
B_i≥s_i; it does not require that new profile to be a minimum. In the
original minimum case it gives

    δ=(1−p)d+p(B_i−s_i)
         +Σ_{j≠i}[Q_j−C_j]^+
      ≥δ+p γ>δ.

Here B_i equals the ORIGINAL cap b_i because that cap strictly exceeds
s_i; the strict source is not being applied to a merely conjectured
minimum tail. All continuation normalizers are positive in this arm.

If the only positive p_i equals one, the prescribed payoff U_i=s_i.
This contradicts the SECOND original-source bound in (7). No conditional
law on the null event that i survives its sure quit is used. Therefore
the first row has at least two positive hazards.

This guarantees some NONSINGLETON stage, not necessarily an exact pair:
other players may quit surely. For example, a sure third quitter prevents
an exact pair stage from being forced by two other positive hazards.
No pair assertion is used.

## 7. Uniform first-row collision mass

The following elementary estimate is included to keep the eventual
original-profile floor independent of the chosen pre-mark tolerance.
No effort is made to optimize its constants. For finite cardinality n≥2
with the strict bounds (7), set

    A=κ/n,       h₀=Aγ/[8M(n+1)],
    σ=A h₀/(n−1)>0.                               (16)

Choose an owner i with p=p_i≥A and put h=Σ_{j≠i}p_j. I claim h≥h₀.
Assume the contrary. These constants satisfy h₀≤δ/(4M)≤1/2 and
2Mh₀<γ, using δ≤2M and n≥2.

If p=1, the owner obtains s_i unless another player joins its first row.
Hence |U_i−s_i|≤2Mh<γ, contrary to (7).

If p<1, every row survival is positive because h<1/2. Conditional
post-row laws therefore have actual finite approximants, with all caps
converging. Their total debt d is at least δ, though not asserted equal
to δ. Form a new actual-carrier profile by moving each opponent's first
row mass into that opponent's OWN conditional tail, leaving i unchanged.
There is no change of dates and no inserted response; only the original
first-row hazards of the opponents are set to zero. Product coupling
changes each payoff and each complete cap by at most 2Mh. Thus its full
debt D_solo satisfies

    D_solo≤δ+4Mn h.                                 (17)

Let B_i be the owner's cap against those conditional opponent tails.
The new owner cap is max(s_i,B_i), so uniform cap coupling and (7)
give max(s_i,B_i)≥s_i+δ+γ−2Mh>s_i. Hence

    B_i−s_i≥δ+γ−2Mh.

The exact solo-row ledger, now used as an inequality for this NEW profile,
gives

    D_solo≥(1−p)d+p(B_i−s_i)
             ≥δ+pγ−2Mp h.

Together with (17) this implies

    Aγ≤pγ≤(4Mn+2Mp)h≤(4n+2)M h
        <(4n+2)M h₀<Aγ,

a contradiction. The finite tail and solo-profile transports here are
valid because each fixed limiting survival is strictly positive; no
uniform lower bound in p over unrelated sources is assumed or needed.

It follows that the first-row probability C(p) of at least two quitters
satisfies

    C(p)≥p[1−∏_{j≠i}(1−p_j)]
         ≥p h/(n−1)≥σ.                             (18)

The middle bound uses union probability at least the largest opposing
hazard, which is at least their sum divided by n−1. This remains correct
at every partly-sure or all-sure boundary. For Fin4, take n=4; σ depends
only on the fixed table's M and actual global gap δ.

## 8. Trace to the original unmodified minimizing sequence

Let a_k be the unique ORIGINAL marked date converging to a. All n
masses at that date converge to p_i. Their cumulative masses STRICTLY
before a_k converge to zero: the corresponding latent threshold is the
LEFT endpoint of a's marked interval, and its limit includes exactly
the mass before a, which is zero by (15). Consequently

    P_original(absorption strictly before a_k)→0;
    Σ_{|S|≥2}P_original(first coalition S at a_k)→C(p)≥σ.  (19)

For clarity, the stage probability for a particular S is

    ∏_{i∈S} p_i^k(a_k)
      ·∏_{j∉S}P_{p_j^k}(τ_j>a_k or τ_j=Never).

The second factors tend to 1−p_j, because each original pre-mark mass
tends to zero. Positive Never masses are not needed. If some p_j=1,
only coalitions containing j can have positive limits, exactly as the
product formula requires. No original player law is modified, and the
WHOLE original profiles still have debt tending to δ.

There are N=2^n−n−1 nonsingleton coalitions. After a further subsequence,
one fixed nonsingleton coalition has original marked stage mass with
liminf at least σ/N. For Fin4 this is σ/11. This is not clock compression or a
replacement by a terminal-coalition atom at an uncontrolled date.

## 9. Uniform early-stage restriction for every actual profile

Let N=2^n−n−1 be the number of nonsingleton coalitions and define σ
by (16). For every ζ>0 there exists ε>0 such that EVERY actual independent
stopping-law profile with D≤δ+ε has an original finite date t and a
nonsingleton coalition S with

    P(absorption strictly before t)≤ζ,
    P(first coalition S at t)≥σ/(2N).                (20)

For Fin4, N=11 and the stage floor is σ/22.

The stage floor is independent of ζ; the required near-minimum tolerance
may depend on ζ. No uniform bound on t is asserted.

If this failed for finite laws at a fixed ζ, choose a sequence with
debt at most δ+1/k violating (20). The marked-calendar construction,
(15)–(19), and the finite coalition pigeonhole give a subsequence and
original dates whose prior absorption tends to zero and whose selected
nonsingleton stage has liminf at least σ/N. This contradicts the assumed
failure for all large indices. For arbitrary stopping laws, first apply
the finite result with tolerance ε₀, then require D≤δ+ε₀/2 and censor
finite mass after a sufficiently late K to Never with debt error below
ε₀/2. Censoring preserves EVERY earlier original stage probability and
its prior absorption exactly. Any positive finite stage in the censored
law is an original date at most K, so its witness transfers unchanged.

This is a genuine original-source restriction under positive global debt,
not an unrestricted equilibrium construction. The residual now has a
large first collision row whose complete caps may involve tied Quit and
Continue branches. The argument neither declares that row cap-Nash nor
controls debt after replacing it by an unrelated auxiliary root.


## 10. Boundary tests and the remaining consumer

**Global minimality is essential.** With one player and singleton reward
1, distribute mass 1−α uniformly on k dates and mass α∈(0,1) at Never.
Its complete cap is 1 and debt α, but each original singleton stage has
mass (1−α)/k. The genuine global minimum is zero, attained by immediate
Quit. Positive debt alone supplies neither the strict minimum margin
nor polynomial constancy at a minimum. The same failure of inference
persists if dummy players are added; no such profile is an alleged
positive global minimum.

**An empty test cannot be inserted beside a tied atom.** For two players
with own singleton 1, passive singleton 0 and pair −10, let each law
assign half its mass to each of dates 0 and 1. The two finite
Quit tests pay −9/2 and −5 respectively, and Never pays 0, so the actual
cap is 0. An invented empty middle date pays 1/2. This is why an atomic
cut retains the literal tied row and removes earlier empty tests only
AFTER its endpoint's cap has been proved strictly above s_i.

**A final finite response is not Never.** With singleton vectors (1,1),
pair (−2,−2), and each law half at date 0 and half at Never, the date-0
test pays −1/2 and Never pays 1/2; their maximum is 1/2. The date-1
test pays 1. The representation keeps the final finite tester distinct
from Never; when finite mass is inserted at c the variation transport
retains the extra empty c⁺ response.

**Without Never floors the coalition need not be a pair.** If three
players quit surely at the first date, every exact-pair stage there
has probability zero and the triple stage has probability one. The
theorem concludes a nonsingleton stage, and the trace preserves any
sure outsiders instead of silently making them Continue. This example
tests the probability statement, not the positive-minimum premise.

**The sure-solo endpoint is handled without a null tail.** When only i
quits at the first date and does so surely, U_i=s_i, regardless of
ghost continuation laws. This contradicts (7) at a genuine minimum.
The proof does not infer tail minimality from a ledger whose tail
coefficient is zero, nor divide by the owner's zero survival.

**The large atom is a FIRST atom of a minimum, not every atom.** No
lower bound is asserted for all atoms of q or for every stage of a
near-minimizing profile. Formula (14) and compact separation produce
one first positive atom. Its isolation is part of the marked source,
not an assumption of a discrete calendar or a positive spacing bound.

**Weak-* semantics do not imply strong likelihood convergence.**
Partition [0,1] into increasingly fine groups of n equal cells and
put r_i^k=n on player i's cell, zero elsewhere. The weak-* limit is 1
for every player, but the density entropy remains n log n rather than
converging to the limit's entropy. No entropy, positive likelihood,
or strong-density assertion enters the proof.

At the produced collision row, let Q_i be first-date Quit value and
C_i the first-date Continue value priced at the ACTUAL tail cap.
Full current caps are max(Q_i,C_i), including all ties. The current
minimum does not force Q_i=C_i, does not make the post-row tail a
minimum, and does not supply a root selected from an auxiliary Nash
game. Consuming this actual collision row while controlling every
cap remains open. No collision erasure or equilibrium conclusion is
silently attached to (A).

## 11. Source comparison and formalization handoff

The relevant established terminal-law atom declaration is
`exists_positive_finiteLawAtom_of_punishmentNormal_minimum_of_not_uniformPayoff`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumLawFiniteAtom.lean`.
It produces positive mass on a nonempty TERMINAL COALITION in a
minimum joint law, under punishment normality. Its companion
`nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff`
retains that point in a causal suffix source. Neither statement forces
a FIRST original chronological collision atom with vanishing original
pre-mark absorption and whole-profile minimality retained.

The declaration
`FinFourTerminalSingletonProducer.exists_singleton_with_stageMass_floor_and_postDateTail_eq`
in `Research/Quitting/FinFourProducerAtlas/Leaves.lean` gives a singleton
stage in the displayed `terminalVertexTargetProfile` and preserves its
post-date semantic tail. Its target is modified; it is not the original
near-minimizing whole profile in (A). These are comparisons with the
literal named scopes, not claims that source-file presence supplies
a new Lean check or that every surrounding route has been audited.

A direct formalization chain is: an arbitrary finite minimizing sequence;
bounded weak-* likelihoods with marked atom endpoints and complete tester
sets; product-kernel and moving-response convergence; actual reweighting
and all-cap transport at EVERY retained cut; endpoint deletion of
nonbinding empty tests; multiaffine constancy and the strict-margin axis
contradiction; compact separation producing the first atom; the full
solo Bellman ledger including the sure endpoint; a quantitative collision
bound; and the ORIGINAL-date trace plus finite-censoring corollary.

The existing semantic pair/carrier definitions and the exact strict
margin declarations provide the source interfaces. New declarations
should produce the marked date and its original stage probabilities
rather than assuming them as fields. The row transport needs its full
mass vector, original left/right marked endpoints, complete caps, and
the original sequence, not only a terminal-coalition probability.
The statement of the uniform corollary must keep its quantifier order:
one fixed table and positive δ determine the stage floor; for EACH
ζ>0 a sufficiently small debt tolerance works for EVERY actual profile.

All new arguments here are ordinary mathematics. The cited declarations
supply the established original-game no-UE bridge and strict source
margins under their actual imports; they do not kernel-check this
marked-calendar producer or its original-profile conclusions. No
ordinary-ℕ realization of the limiting q, simultaneous realization of
an arbitrary counterfactual table, full finite-horizon equilibrium,
uniform-equilibrium construction, or unrestricted counterexample is
asserted. The exact new conclusion is the necessary collision-stage
restriction (A) on every positive global-gap table in the stated scope.
