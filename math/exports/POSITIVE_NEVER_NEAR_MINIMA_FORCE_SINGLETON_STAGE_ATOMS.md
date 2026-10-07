# Positive-Never near-minima force an original singleton stage atom

## 1. Main original-profile restriction

Consider any nonempty finite player set I, with n=|I|, and any real
reward vector r(S) for each nonempty coalition S⊆I. At the first date
with one or more Quit actions the game absorbs at that coalition's
reward; perpetual Continue has terminal reward zero. Private behavioral
randomization is independent. Before absorption the only public history
is all Continue, so each behavioral strategy is represented by a stopping
law on ℕ∪{Never}. No public correlation or restriction on deviations is used.

Write U_i(p) for terminal payoff, b_i(p) for the supremum against ALL
behavioral deviations, and

    D(p)=Σ_i[b_i(p)−U_i(p)],       δ=inf_p D(p).

The same cap is the supremum over every pure finite stopping date and
Never. The same infimum results from finite-support laws, as proved below.
For an actual profile define its singleton STAGE probability by

    m_i(t;p)=p_i({t})∏_{j≠i}p_j({t+1,t+2,…,Never}).

This is the probability that the ORIGINAL prescribed profile first
absorbs at date t with exactly player i quitting. It is not a hazard
conditional on survival, an aggregate terminal coalition probability,
or a counterfactual stage produced by altering a player's action.

**Theorem.** If δ>0, then for every η>0 there exist ε>0 and γ>0 such that
EVERY actual independent stopping-law profile p satisfies

    D(p)≤δ+ε and p_i(Never)≥η for all i
       ⇒ ∃i∈I ∃t∈ℕ : m_i(t;p)≥γ.                (A)

The profile may use infinitely many finite dates. The same claim therefore
holds for unrestricted behavioral profiles through their stopping laws.
The constants depend on the fixed table and η; no effective formula
for them is asserted.

A sequence version retains more geometric information. Start with any
specified finite-law sequence p^k with D(p^k)→δ. It has a marked ordered
subsequence representation preserving all payoffs, complete caps, and
first-coalition probabilities. If every limiting Never mass is positive,
some retained finite atom traces to original dates t_k and a fixed player
i with

    liminf_k m_i(t_k;p^k)>0.                       (B)

No p^k is changed in this conclusion. In particular, its WHOLE-PROFILE
near-minimality is retained, not merely its post-date continuation.
The original dates may diverge; no common finite time bound is claimed.

The proof first constructs the actual numerical minimum on a compact
marked calendar. Small prefix erasure then preserves this genuine minimum.
Completely diffuse finite marginals with all Never masses positive would
allow finitely many such erasures followed by the all-Never limit,
contradicting the global singleton margin. Finally a retained finite atom
is traced back to the unchanged original profiles.

These are ordinary mathematical results. They provide a necessary
restriction on every positive global terminal-debt gap, not a proof of
uniform-equilibrium existence, a counterexample, or a Lean verification
of the new statements. They apply to arbitrary finite n and signed
rewards; the original-game no-UE interpretation is specified in Section 3.

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

## 3. Original semantic source and the global singleton margin

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
necessary original-table restriction on every no-UE game, without a
normalization or a supplied strategy witness.

The finite-support approximation declaration inspected is
`exists_finiteDeadlineTimingProfile_approximation` in
`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`.
The elementary uniform-cap coupling in Section 2 proves the exact
sum-debt approximation needed here without silently substituting a
maximum-debt objective.

## 4. Erasing a small cap-inactive prefix

Let q,T,c be the represented source of Section 2 and let δ=D_*>0.
Its prescribed-payoff/cap pair is in the original terminal-semantic carrier,
because one actual sequence converges to both coordinates. It minimizes
sum debt there by continuity. The inspected declaration
`minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
therefore gives, for every i,

    b_i(q)−s_i≥δ,       s_i=r_i({i}).             (7)

This is a SUM-debt statement. No all-player debt tie from a maximum-debt
minimum is imported. In particular δ≤2M.

Choose an available finite cut a∈T with q_i({a})=0 for all i. Put
x_i=q_i({t∈T:t<a}) and suppose

    Σ_i x_i≤δ/(4M).                              (8)

Each x_i<1. Let q_i^+ be q_i conditioned on t≥a, including Never.
The claim is

    D_{T∩[a,c]}(q^+)=δ.                          (9)

The cap includes a and Never; since a is non-atomic, its forced-Quit payoff
is s_i. Thus removing the now-empty earlier dates does not remove a cap test.
This specific point is why (9) is not asserted for a cut at a positive atom
with no preceding available empty response.

For x_i>0 let q_i^- be the conditional prefix law. Hold these two laws fixed
and let z_i be their mixture mass, forming

    q_i^z=z_i q_i^-+(1−z_i)q_i^+.

Coordinates with x_i=0 stay fixed at z_i=0. These are actual admissible
represented-law variations, although they are not merely an application
of the finite-atomic formula (2). Here is their separate transport.
Use the finite realizing sequence from Section 2 and split each original
law at the set of original locations strictly below a. Because q has no
atom at a, the corresponding prefix probabilities x_i^k converge to x_i.
For x_i>0, reweight each finite prefix and suffix by z_i/x_i^k and
(1−z_i)/(1−x_i^k), respectively. These are exactly normalized probability
laws. Zero-prefix coordinates are left unchanged. The factors converge
to z_i/x_i and (1−z_i)/(1−x_i) and are bounded for fixed z, while the
prefix indicator converges almost everywhere
in the common quantile chart. The product weak-* and moving-kernel proof
(3)–(6) therefore applies to these reweighted laws. No dates are inserted
or deleted: all old tests remain available, even where their new prescribed
mass is zero. Complete caps and prescribed payoffs converge. Hence

    D_T(q^z)≥δ                                   (10)

for every such z∈[0,1]^J, where J={i:x_i>0}. In particular this is not an
orbit-minimum hypothesis or a conditional-law selection assumed without proof.

For a response strictly before a, no opponent stops before or together with
the responder except on an event of probability at most Σ_{j≠i}z_j. Therefore
its payoff is at most

    s_i+2MΣ_{j≠i}z_j.                            (11)

The cap over responses at or after a, including Never, has the exact form

    L_i(z)=A_i(z₋ᵢ)+[∏_{j≠i}(1−z_j)] b_i(q^+).

Here A_i is the expected passive payoff from the first opponent prefix
coalition; it is multiaffine in z₋ᵢ. The prescribed U_i(q^z) is multiaffine
in all coordinates. Consequently

    P(z)=Σ_i[L_i(z)−U_i(q^z)]

is a multiaffine polynomial. At z=x, (7), (8) and (11) give a strict
gap of at least δ/2 between every early response and its full cap. The same
gap remains positive in a neighborhood of x. Thus D_T(q^z)=P(z) there.
By (10), x is a local minimum of P, interior in all coordinates J.

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
a global sum-debt minimum. Therefore (7) applies to that point too.
Meanwhile (11) and Σz(t)≤Σx bound every early response by s_i+δ/2.
No early response can attain its cap. This is a uniform strict gap, so
nearby t still has D=P=δ. Hence C is also relatively open. Connectedness
gives C=[0,1]. At t=1 there is no prefix mass and all old prefix tests
equal the own singleton payoff, already attained by the empty test a.
This proves (9).

The preservation uses all cap tests, not a chosen cap witness. It also
uses global minimality twice: first to make the multiaffine branch locally
minimal, then to prevent a new early cap from binding during continuation
to z=0. A mere inequality for the derivative at one point would not justify
the continuation step.

The result does not erase a large atomic prefix, does not choose an available
non-atomic cut when none exists, and does not establish arbitrary repeated
suffix renewal through a zero-reach limit. Those are genuine remaining
boundaries. The conclusion removes an initial cap-inactive segment at
the actual positive minimum while keeping the entire remaining
chronological law. No selected prefix-orbit minimum or auxiliary
equilibrium replaces that law.

## 5. Excluding completely diffuse positive-Never minima

The represented genuine minimum of Section 2 cannot satisfy both

    α_i=q_i(Never)>0 for every i,
    q_i({t})=0 for every i and every finite t∈T.    (12)

This theorem uses the numerical GLOBAL minimum δ=D_*>0, not a profile
with positive debt, or a minimum along one selected orbit. Rewards may
have either sign. It consumes a source branch; it does not prove UE for
arbitrary data or say that every positive minimum must have zero Never.

Choose M>0 bounding all rewards. The true singleton moat gives δ≤2M.
Set

    κ=δ/(4M)∈(0,1/2],       ρ=∏_i α_i>0.

For an available cut a∈T, let

    S_i(a)=q_i([a,c]∪{Never}),
    R(a)=∏_i S_i(a),
    q_i^a=q_i conditioned on [a,c]∪{Never}.

All these conditionings are defined because S_i(a)≥α_i>0. In particular
R(a)≥ρ. Under (12), every retained cut is nonatomic. The initial cut
a₀=min T has q^{a₀}=q; the degenerate all-Never case is already impossible
at a positive global minimum by the argument below.

### The actual source regenerates under each finite conditioning

Whenever a finite sequence of Section 4 erasures has reached a,
q^a is a genuine global-minimum suffix on T∩[a,c]. Every formerly earlier
empty response pays s_i, already represented by the available empty
test a. Thus none of its complete tests has been dropped.

The next use of Section 4 does not assume a new representation with
the same atomlessness. It reuses the ORIGINAL finite realizing sequence.
Take original test locations a_k→a and restrict every original marginal
to times at or after that test, including Never, then normalize. The
boundary mass is zero, so the normalizers converge to S_i(a)≥α_i.
The normalized densities on the original common quantile chart remain
bounded by, for example, 2n/min_i α_i at sufficiently large indices.
Their weak-* limits are the corresponding conditional densities, and
the same moving response kernels retain all tests at or after a.
Shift the retained first test to original date 0; this is an order
preserving change of integer labels, not an inserted empty stage.
It yields actual finite profiles with the full payoff/cap limit q^a.

Conditioning again at b>a is exactly conditioning the original law at b.
For any fixed finite number of iterations the cumulative normalizer is
1/S_i(b), still bounded by 1/α_i, rather than an uncontrolled product
of approximation errors. At each new step the singleton moat applies
to this actual carrier minimum. The finite head/suffix reweighting in
Section 4 therefore remains valid with this inherited realizing
sequence. No simultaneous realization of infinitely many counterfactual
updates, nor an ordinary-ℕ realization of q, is required.

### A fixed amount of erased head spends a finite survival budget

At a current minimum suffix define its total conditional finite mass

    Λ(a)=Σ_i[1−α_i/S_i(a)].

If Λ(a)>κ, atomlessness makes

    H_a(b)=Σ_i q_i^a([a,b))

a continuous nondecreasing function of real b, from 0 at a to Λ(a)
at c. There is a b∈T with a<b<c and H_a(b)=κ. Indeed the intermediate
value theorem supplies such a real cut; if it lies in a gap of T, move
it to a gap endpoint without changing H_a. Equivalently choose a
boundary point of the level set, which lies in the union of the finite
marginal supports. All these points are still nonatomic by (12).

Section 4 applies to this complete conditional prefix: its removed
masses x_i=q_i^a([a,b)) have sum κ. Consequently q^b is again a genuine
global minimum, and

    R(b)=R(a)∏_i(1−x_i)≤R(a)exp(−κ).           (13)

If the branch Λ>κ lasted N steps, then R≤exp(−Nκ), whereas always
R≥ρ. Choose a finite integer N with exp(−Nκ)<ρ. It follows that the
iteration reaches some minimum suffix a with Λ(a)≤κ in fewer than
N steps. This is a finite argument: no source limit is inferred from
an unending renewal construction.

### The remaining small suffix would make all Never minimal

At that final a, every later available cut b<c removes total conditional
mass at most Λ(a)≤κ. A further application of Section 4 thus shows
that q^b is a global minimum for EVERY such b. Under (12), take
available b increasing to the upper endpoint of the finite support;
using c is equivalent if there is an empty final gap. If no finite
mass remains, the suffix is already all Never. Otherwise cuts in the
finite support exist approaching that endpoint and their residual finite
mass tends to zero, since there is no terminal atom. For each i,

    q_i^b(Never)=α_i/S_i(b)→1.

Hence q^b tends to all Never in total variation. The original reward
bound controls every pure deviation uniformly by the probability that
some opponent's clock changes. Thus the complete caps tend to
max(s_i,0), and prescribed payoffs tend to zero, even though the retained
suffix calendar changes. Its first available cut always provides the
finite singleton test; Never remains separate. Consequently

    δ=Σ_i max(s_i,0).

The right side is the debt of the ACTUAL all-Never profile. It would
therefore be a positive global minimum. If all s_i≤0 that debt is zero,
an immediate contradiction. Otherwise choose j with s_j>0. The global
singleton moat at all Never gives

    δ≤max(s_j,0)−s_j=0,

again impossible. This proves the exclusion (12).

### What was, and was not, consumed

This excludes every completely diffuse represented minimum with all
Never masses positive, regardless of which finite or Never responses
attain the complete caps. The positive original joint-Never probability
is used as a lower bound on the total remaining survival, not as a
denominator for an uncontrolled near-minimum error.

The conclusion is that every represented positive minimum has either
a zero-Never player or a positive finite atom. It does not give a lower
bound on that atom. With atoms, a cumulative-mass cut may jump across
the admissible κ budget; in addition, adjacent retained atomic times
need not have an available empty response between them. An invented
empty cut can change the complete cap. Thus the above proof must not
be relabeled as a macroscopic-atom theorem or silently iterated through
atomic endpoints. Consuming those collisions, or the zero-Never branches,
remains necessary for an arbitrary-table conclusion.

## 6. Tracing an atom to the same original minimizing sequence

Assume every represented Never mass α_j is positive. Section 5 supplies
a player i and a finite location t∈T with w=q_i({t})>0.
In the construction of Section 2, the identity part of π on E cannot
give a point positive mass: every r_i dx is absolutely continuous with
respect to Lebesgue measure. Therefore t is the midpoint of a genuine
component J=(a,b) of [0,c] outside E, with b>a.

There is exactly one original atom interval J_k=(a_k,b_k) converging to J.
Let t_k be its ORIGINAL finite date. Since the likelihoods are uniformly
bounded, moving the two endpoints costs o(1), and weak-* convergence on
the fixed interval J gives

    p_i^k({t_k})=∫_{J_k}r_i^k → ∫_J r_i=w.

Similarly the original Never intervals (c_k,1) converge to (c,1), so

    p_j^k(Never)→α_j for every j.

For these unchanged profiles, the exact first-singleton event satisfies

    m_i(t_k;p^k)
       =p_i^k({t_k})∏_{j≠i}p_j^k({t_k+1,t_k+2,…,Never})
       ≥p_i^k({t_k})∏_{j≠i}p_j^k(Never).

The last expression converges to w∏_{j≠i}α_j>0. For example, half this
positive limit is an eventual stage floor, proving (B).
The event in the product already ensures that no opponent stopped
earlier. Nothing has been conditioned away from the original stage
probability, and the atom interval is tied to one actual original date,
not to a newly compressed clock.

This is where positive Never masses perform a second role beyond the
survival budget in Section 5. Without them, a positive marginal clock
atom need not carry any prescribed singleton STAGE probability: another
player may surely stop earlier. The argument does not discard that
possibility in the zero-Never branch.

## 7. Uniform near-minimum stage floor for all actual laws

Fix η>0. Suppose the theorem (A) failed. For every integer k≥1 choose
an actual law profile p^k with

    D(p^k)≤δ+1/k,       p_i^k(Never)≥η for every i,
    m_i(t;p^k)<1/k for every i and t.

First suppose the p^k have finite support. Apply Section 2 to THIS
sequence. Its limiting Never masses satisfy α_i≥η. Sections 5 and 6
then produce a fixed player and original dates with a positive eventual
stage floor, contradicting the displayed bound. This proves the uniform
ε,γ assertion for finite laws, not merely the existence of one specially
selected stage-bearing sequence.

For arbitrary laws, censor each p^k after a sufficiently late finite
deadline K_k by moving its finite mass after K_k to Never. Uniform-cap
coupling makes the resulting finite profile p̃^k satisfy
D(p̃^k)≤δ+2/k. Its Never probabilities can only increase.
For every t≤K_k its original stage probabilities are EXACTLY preserved:
censoring later dates to Never does not change any event {τ_j>t}.
For t>K_k its finite stage probabilities are zero. Thus every singleton
stage of p̃^k is still <1/k, giving the same contradiction.
This proves (A) for unrestricted stopping laws and hence behavioral play.

The proof is non-effective compactness. It asserts neither a universal
table-independent γ nor an explicit rate in η or δ. It also does not
modify the profile to which the conclusion (A) applies. The temporary
censoring is used only in the contradiction proof, and any resulting
stage floor transfers to the very same earlier stage of the original law.

## 8. Boundary tests and source distinction

**The last finite test is not Never.** For two players with both singleton
vectors (1,1) and pair vector (−2,−2), give each player half its mass at
a finite c and half at Never. Testing only {c,Never} gives cap 1/2,
whereas a finite test strictly after c gives cap 1. This is why the
finite-atomic variation theorem retains c⁺.

**A missing intermediate test cannot be inserted freely.** For two
players with own singleton 1, passive singleton 0 and pair −10, give
both laws equal mass on two adjacent dates. Their actual cap is 0.
An inserted empty middle date would give 1/2. The sets of original
response locations T_k, not just the atom endpoints E_k, prevent
this false change of game.

**Positive debt alone is insufficient.** For one player with singleton
reward 1, put mass α∈(0,1) at Never and distribute mass 1−α uniformly
over k finite dates. Its complete cap is 1, its payoff is 1−α, and its
debt is α, while every singleton stage has mass (1−α)/k→0.
The represented finite part can be diffuse and its Never mass stays α.
This is not a counterexample to (A): the TRUE global minimum is zero,
attained by immediate Quit. The whole-minimum hypothesis is essential.

**Weak-* semantic convergence is not strong density convergence.**
Partition [0,1] into increasingly fine groups of n equal cells and put
r_i^k=n on player i's cell and zero on the others. Then r_i^k⇀*1, while
Σ_i∫r_i^k log r_i^k=n log n does not approach the entropy of the limit.
No entropy convergence, lower likelihood bound or common support
positivity is used by the theorem.

**No atom-size floor is inferred from nonatomic cuts alone.**
Section 5 proves that a finite atom exists, and Section 6 traces that
particular atom. It does not assert a universal marginal atom size or
that every atom is large. Isolated positive atomic dates may have no
available empty tester between them, even when their masses are small.
The near-minimum stage floor (A) has different quantifiers: for a FIXED
table and a FIXED lower Never bound, sufficiently near-minimal whole
profiles must have SOME singleton stage of positive size.

There are two relevant existing source comparisons. The declaration
`exists_positive_finiteLawAtom_of_punishmentNormal_minimum_of_not_uniformPayoff`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumLawFiniteAtom.lean`
produces positive mass on a nonempty TERMINAL COALITION in a minimum joint
law. It does not locate a marginal time atom or an original stage, and
its statement includes punishment normality. The same file's
`nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff`
retains that minimum point in a causal source construction.

Separately,
`FinFourTerminalSingletonProducer.exists_singleton_with_stageMass_floor_and_postDateTail_eq`
in `Research/Quitting/FinFourProducerAtlas/Leaves.lean` gives a literal
singleton stage in a selected endpoint target profile and identifies
its post-date semantic tail. Its target is the displayed
`terminalVertexTargetProfile`, not the unmodified near-minimizing whole
profile. These inspected declarations do not state (A) or (B).
No broader absence-of-overlap claim is made beyond their exact scopes.

The new restriction preserves the original table, probability mode,
unrestricted deviation caps, and WHOLE-PROFILE near-minimality. Its
remaining alternatives are genuine: Never probabilities may approach
zero, or the forced original stage atoms may still have unconsumed
interaction and cap effects. Nothing here converts a clock atom to
an equilibrium or contradicts every positive gap.

## 9. Mathematical and implementation boundary

The statements assembled here are ordinary mathematics. The named source
declarations supply the established original-game bridge and global
singleton margin under their actual imports. Their presence does not
kernel-check the marked-calendar construction, prefix erasure,
diffuse exclusion, or the new original-stage conclusions.

A direct formalization chain is: bounded weak-* likelihood subsequence
with marked atom endpoints and complete tester sets; product-kernel and
moving-tester convergence; exact all-cap finite transport; global
small-prefix erasure; finite positive-Never survival-budget exclusion;
same-sequence atom trace; and the uniform near-minimum stage corollary.
The strategic input is arbitrary original reward data plus the actual
positive global debt infimum. No equilibrium rates, support, continuation,
or favorable response selector is supplied as an extra premise.

An ordinary ℕ realization of the limiting compact-calendar minimum is
not asserted. Neither are arbitrary compact-calendar variations,
simultaneous realization of all counterfactual replacements, a renewable
paid chronology, a uniform-equilibrium construction, or a positive-gap
counterexample. The result is a strict actual-profile restriction that
every such counterexample would have to satisfy.
