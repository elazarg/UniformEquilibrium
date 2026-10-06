# Four-player quitting-game frontier

The four-player uniform-equilibrium conjecture is open. No table with a
certified positive gap against every behavioral profile is known in the project.

“Tracked theorem” below means a result represented by the named Lean declarations.
“Mathematical result” identifies an additional proved reduction or exclusion
awaiting formalization; it is not being counted as an implemented theorem.

## 1. Objective and semantic quantities

Players are I={0,1,2,3}. A reward table has one vector r(S) for every nonempty
S⊆I: sixty real coordinates. Live play and Never pay zero. Before absorption
the public history is only repeated all-Continue. A behavioral profile is
equivalently four independent laws on ℕ∪{Never}; a deviator replaces one
complete law, including arbitrary late times and Never.

For an actual profile p define

    Uᵢ(p) = prescribed expected terminal payoff,
    Bᵢ(p) = supremum payoff over all replacements of player i,
    dᵢ(p) = Bᵢ(p)−Uᵢ(p),
    E(p) = maxᵢ dᵢ(p),        D(p) = ∑ᵢ dᵢ(p),
    η(r) = infₚ E(p),         D*(r) = infₚ D(p).

Then η≤D*≤4η. The exact positive and negative endpoints are:

- UE(r) ⇔ η(r)=0.
- No UE(r) ⇔ η(r)>0 ⇔ D*(r)>0.

UE(r) means one fixed vector v such that, for every ε>0, one behavioral
profile and one horizon threshold work for every larger horizon: expected
average payoffs are within ε of v coordinatewise and every complete unilateral deviation
gains at most ε. The target precedes ε; the profile may depend on ε.

A lower bound η≥γ>0 supplies an actual profitable response at every gain
threshold below γ; cap attainment at γ is not implied.

The compact semantic carrier is the closure of actual pairs (U,B). The joint
carrier additionally retains the complete first-coalition law, including
Never. Both objective minima are attained on these carriers. Their minimizing
points need not be actual profiles, and minimizing E is not minimizing D.

## 2. Available reductions of reward data

### Single-pivot normalization — tracked theorem

Existence of any Fin4 counterexample is equivalent to existence of one with

    s=(1,0,0,0),        sᵢ=rᵢ({i}),

after choosing the pivot label. All other reward entries remain unrestricted.
The theorem includes actual semantic transport; it is not justified merely
by subtracting constants while leaving Never fixed.

Common positive scaling can additionally put every reward in [−1,1]. The
singleton vector then has the form λeₚ with λ>0, not necessarily eₚ.
Player relabeling preserves UE.

### Rational approximation — tracked theorem

For entrywise reward distance Δ,

    |η(r)−η(r′)| ≤ 2Δ.

A positive-gap table therefore has an open neighborhood of positive-gap tables
and yields a bounded rational counterexample. Counterexamples cannot exist
only on a measure-zero exceptional reward locus.

Rational approximation, single-pivot normalization, and the next generic-fiber
selection are distinct reductions. Preservation of one reduction's selected
minimum, law, or ancestry under another is not supplied automatically.

### Generic singleton-fiber selection — mathematical result

Separate the four own-singleton entries s from the other 56 coordinates b.
A screened root is an independent date-zero root with at least two sure
quitters, followed by Never. Define

    Ω_b = max[s∈[−1,1]⁴] η(r_b(s)),
    θ(b) = min[screened roots q] E(q).

The screened minimum is independent of s. There is an explicit nonzero
integer polynomial Π(b), of degree 144, such that Π(b)≠0 excludes four equal
positive complete debts at every screened root, including mixed roots.

If any Fin4 counterexample exists, one can select

    b∈ℚ⁵⁶∩(−1,1)⁵⁶,    Π(b)≠0,    Ω_b>0,    θ(b)>Ω_b.

The maximizing singleton vector need not be rational.

At every positive maximum-regret minimum on this fiber, the total singleton
law mass is positive. More strongly, for each a>0 there are κ,ε₀>0 such that,
uniformly over all s with η(r_b(s))≥a, every actual profile p satisfies

    E(p)≤η(r_b(s))+ε₀  ⇒  ∑ᵢ Prₚ(first coalition={i})≥κ.

This collar attaches to the same actual common-calendar near-minimizers,
tester weights, first-order stationarity, and total singleton-pressure
inequality produced by finite optimization on the selected fiber.
It excludes zero-singleton minimum laws after selection. It does not provide
a fixed-date atom, a counterfactual singleton floor, or cap control after a
response. The construction does not retain the earlier membership-stretch
ancestry or assert a simultaneous single-pivot normal form.

### Single-pivot secant and strict-pressure selection — mathematical result

There is a separate counterexample-source reduction that retains three zero
own-singleton rewards. If a counterexample exists, select rational frozen
coordinates b∈(−1,1)⁵⁶, rational t∈(0,1), and α>0. Write rˣ for the table
with own singletons (x,0,0,0), e(x)=η(rˣ), and
z(p)=Prₚ(first coalition={0}). One fixed ξ∈(t,1) can be selected with

    e(t)>2α,          3α/4≤m=e(ξ)≤α,
    E_rξ(p)+(ξ−t)z(p)≥e(t)             for every actual p.

Consequently every near-minimizer with E_rξ(p)≤m+α/4 has z(p)≥3α/4.
The inequality also holds on the joint semantic/law carrier. This is a
pivot-specific collar, without a genericity or screened-root premise.

On the same fixed table there are actual independent finite-clock
near-minimizers and tester weights with vanishing weighted inactivity,
vanishing first-order error against every enlarged-calendar competitor,
and pivot pressure at most −α/4 in the limit. Pivot pressure is the weighted
change of z under pure pivot responses; other owners' testers contribute zero.
Every owner has tester weight eventually at least m/4.

These fields produce an arbitrarily near-best finite pivot reply removing
at least α/16 of z. Delaying only the pivot's private clock to that deadline
also removes at least α/16, loses at most the requested payoff error, and
preserves the pivot's full cap exactly. The other three caps are uncontrolled;
neither modification is proved to remain near the minimum. The mass loss is
therefore not a renewable rank.

This source uses a tilted one-coordinate maximum, not a maximum over all
four own-singleton entries. Strict pivot pressure does not additionally
assert the preceding source's nonpositive total pressure. The final ξ need
not be rational.

## 3. Exact conjecture-equivalent formulations

### A. Independent finite-law selection

Tracked finite-menu approximation gives, for every actual profile and every
ε>0, finite stopping laws with prescribed payoff error below ε and full
exploitability at most the original exploitability plus ε.

On a canonical single-pivot table, use the menu
F_N={0,…,N−1,Never}. For a product law p let E_N(p) be regret against that
same menu, Wₚ(p) the pivot's Never payoff, and

    Zₚ(p) = ∏[j≠pivot] pⱼ(Never).

The exact unrestricted formula is

    E(p)=max(E_N(p), Wₚ(p)+Zₚ(p)−Uₚ(p)).

Thus the unresolved source theorem is

    for every ε>0, choose N and one independent p on F_N
    with E_N(p)≤ε and Wₚ(p)+Zₚ(p)−Uₚ(p)≤ε.

No nesting across ε is required. Exact menu Nash is neither required nor
sufficient.

For fixed finite opponent laws, a compact finite affine program attains a
value equal to infimum full exploitability over every pivot behavioral law.
A minimizing program point may require approximating strategies rather than
one attaining strategy. The remaining optimization is over the three
independent opponent laws; the inner program does not select them.

### B. Bounded approximate forward packets or a sure root

Let |rᵢ(S)|≤M, let μᵢ be the infimum over independent opponent plans of
the unrestricted response cap, and assume μᵢ≤sᵢ for all i with some sᵢ>0.
These hypotheses are available after single-pivot normalization.

For q∈[0,1]⁴ put

    c(q)=∏ᵢ(1−qᵢ),       a(q)=1−c(q),
    F(v,q)=c(q)v+∑[S≠∅]Pr_q(S)r(S).

Let eᵢ(v,q) be ordinary one-stage regret against continuation v: the larger
of Quit and Continue endpoint payoffs, minus Fᵢ(v,q). Set K=[−M−2,M+2]⁴.

A tracked equivalence is

    UE(r) ⇔ weighted forward packets in K
             or an exact Nash root against μ with a sure quitter.

The packet premise means: for every δ>0 and requested charge Q≥0, there is
one finite sequence v₀,…,v_H∈K and roots q₀,…,q_{H−1} such that

    |v_{t+1}(i)−Fᵢ(v_t,q_t)|≤δa(q_t),
    eᵢ(v_t,q_t)≤δa(q_t),          ∑[t<H]a(q_t)≥Q.

K is fixed before δ and Q. The construction runs by outward prefixing;
play order reverses the root word. Annotations need not be actual tail
payoffs. No punishment-floor input is required.

The open producer must establish one of the two alternatives from the
remaining reward data. The equivalence itself does not supply them.

### C. Compact invariant barrier

A tracked exact negative formulation is a table, γ>0, and a closed set C
inside the bounded payoff/cap box such that

- C contains the all-Never semantic pair;
- C is invariant under prefixing every independent product root;
- maxᵢ(Bᵢ−Uᵢ)≥γ at every point of C.

The prefix cap uses the maximum of Quit-now and Continue followed by the
full old cap. Invariance is not restricted to Nash roots or selected responses.
Such a barrier exists iff η≥γ; the full semantic carrier is one when η≥γ.

The open task is to construct a positive barrier for one table or exclude
positive barriers for all Fin4 tables. A barrier around one response cycle
does not suffice unless it meets these universal closure conditions.

### D. Rational polynomial obstruction

Under the normal positive-singleton assumptions of B, a tracked equivalence is

    No UE(r) ⇔ no punishment-vector sure root
               and a rational full robust polynomial potential exists.

Precisely, there are rational 0<τ≤1/4 and a rational-coefficient polynomial P
such that

    P(v)−P(u)≥a(q)

for every v,u∈K and every product q satisfying

    |uᵢ−Fᵢ(v,q)|≤τa(q),        eᵢ(v,q)≤τa(q),     for all i.

This is a complete negative certificate language: the forward direction
produces P from no UE. It does not assume a polynomial producer.

The table normalization and polynomial restrictions hold simultaneously.
Existence of any real Fin4 counterexample is equivalent to existence of one
unit-bounded table with own singletons λeₚ, λ>0, no punishment-vector sure
root, and one rational polynomial P on [−3,3]⁴ satisfying the full robust
inequality, total degree at least three, failure of multi-affinity, and the
adaptive minimum conditions in Section 4. The forward construction permits
λ=1/N for a positive integer N. The reward table need not be rational; the
certificate is rational. These are restrictions on one produced table and
one polynomial, not certificates selected on different normalizations.

The open task is to exhibit a table, the absent-sure-root condition, and such
a P, or to prove that every candidate fails some full-relation edge.
No polynomial degree bound or universal finite search cutoff is known.

## 4. Restrictions on the polynomial obstruction

The degree, multi-affinity, and adaptive minimum restrictions are tracked
together for the same bounded single-pivot obstruction. The following shape
restrictions explain the remaining class.

- On the full exact-root relation for a bounded finite signed table, a
  continuous potential differentiable near the singleton upper rectangle
  cannot be quasiconvex there. This exclusion needs no matrix hypothesis.
- Under the standard-Q singleton-matrix condition, face drift also excludes
  additive potentials and regular scalar transforms of additive potentials;
  robust drift forces quantitative mixed and negative curvature.
- For |r|≤1 and sᵢ≥0, on the full box [−3,3]⁴, no quadratic polynomial
  (including an indefinite one) and no multi-affine polynomial is a potential.
  Monotone C¹ scalar transforms of these classes are also excluded.
- Every global minimum a of a surviving smooth potential satisfies aᵢ>sᵢ
  for all i; upper-box boundary coordinates are allowed. A reflected
  segment on which the restriction rises and falls forces a quantitative
  positive directional third derivative.

More precisely, put g=minᵢ(aᵢ−sᵢ)>0. There is a minimizer x of P on the
lower boundary of ∏ᵢ[sᵢ,max(aᵢ,1)] such that

    ∇P(x)·(x−a)≤−g/2,
    a+t(x−a)∈[−3,3]⁴                    for every 0≤t≤2,
    D³P(a+t₀(x−a))[x−a,x−a,x−a]≥3g      for some 0<t₀<2.

On 0≤t≤1 the same restriction has an interior maximum strictly above
both endpoint values. These witnesses are produced for every global
minimum of the same polynomial; they are not extra assumptions on a.

After the actual single-pivot reduction and scaling, the last two exclusions
lose no hypothetical counterexample. A remaining polynomial must have total
degree at least three and repeated-coordinate powers. Necessary face or
curvature inequalities are not sufficient for the full robust inequality.

### Selected exact-root return — tracked conditional consumer

Assume sᵢ≥0. Let R=∑[S≠∅,i]|rᵢ(S)| and choose R<B≤R+2.
If every v∈[−B,B]⁴ with some vᵢ<sᵢ admits an exact Nash root q
against v with some Fⱼ(v,q)≤sⱼ, then the game has UE. The selected
root need not be unique or vary continuously, and other roots may have
every successor coordinate above its singleton.

This is `exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_on_subbox`
(`UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`).
Its boxed-return hypothesis is not produced by the consumer. The displayed
implemented wrapper uses the summed bound R; the generic analytic exclusion
accepts a supplied coordinate reward bound strictly below B. Raw
criteria using smaller boxes can use that analytic theorem with the
polynomial obstruction directly, rather than identifying R with the maximum
absolute reward entry. No universal selected-return theorem is asserted.

## 5. Minimum geometry and the paid-response route

### Maximum regret — tracked theorem, with a mathematical strengthening

At every positive global maximum-regret minimum m on the semantic carrier,

    dᵢ=m for every i,       Bᵢ−sᵢ≥m.

The additional harmonic argument proves

    ∑ᵢ m/(Bᵢ−sᵢ)≤1.

For a unit-bounded Fin4 table it gives η(r)<1/3, and compactness gives a
worst unit-cube value strictly below 1/3. This is a positive-error upper
bound, not a vanishing-regret theorem.

### Total debt — tracked source reduction

From no Fin4 UE, the law-tight global-minimum construction supplies a
positive finite coalition atom and either

1. a minimum with all four debt coordinates positive; or
2. a reset-rigid same-law minimum return with a zero-debt coordinate,
   positive opponent incidence, and a supported strict terminal toggle.

Every exact cap-Nash prefix of a positive total-debt minimum is all Continue:
prefixing scales every debt by joint survival, and any absorption would
contradict global minimality. The cap margin is Bᵢ−sᵢ≥D*>0.

Actual finite chains of unilateral replacements, quantitative paid rows, and
source reconstruction are available. A tangent paid-row construction fixes
a nonmover with limiting debt at least D*/3, eventual debt at least D*/4,
and a pure-response gain at least D*/16, with actual reach bounds.
These are produced response data, not a Nash–Bellman block.

For an actual replacement of player i with payoff gain g,

    Bᵢ(new)=Bᵢ(old),
    dᵢ(new)=dᵢ(old)−g,
    D(new)−D(old)=−g+∑[j≠i](dⱼ(new)−dⱼ(old)).

The other debts may increase or enter previously zero coordinates.
On minimum-fiber response chords, coordinate debt is affine; at every
strictly interior chord point, support is the union of endpoint supports.
Specified no-entry/full-replacement
branches have renewable strict support descent. An arbitrary returned
minimum does not inherit that rank decrease.

Open consumers remain for the full-debt and reset-rigid chambers and for
their off-minimum paid outputs. Required conclusions are actual debt below
the original D*, a consumed charged return, or a genuinely renewable rank
whose every terminal case is consumed. Merely generating another paid row,
a new minimum, or a real-valued decrease does not supply those conclusions.

### Finite cap-threshold descent — tracked theorem

Call i preempted if some j≠i has sⱼ>rⱼ({i}). For an arbitrary actual source p
with D(p)>0, a preempted i, and |r|≤M, set

    C=max(D(p), Bᵢ(p)−sᵢ).

There is a finite product-root word w, followed by the literal old profile,
such that

    D(w::p)≤C−3C²/(32M+6C).

If Bᵢ−sᵢ≤D, this strictly decreases the incoming debt. If Bᵢ−sᵢ>D, it
need not. With nonnegative own singletons, weak payoff exclusion supplies
renewed usable owners or an unpreempted-owner solo exit, giving a terminating
selector. Arbitrary remaining tables have no such renewal theorem.

At every positive total-debt minimum of a signed Fin4 table, the same
argument strengthens the minimum margin to

    Bᵢ−sᵢ≥D*+(D*)²/(8M),
    Uᵢ−sᵢ≥D*−dᵢ+(D*)²/(8M)>0.

Thus a minimum cannot itself supply the usable-owner condition. This
quantitative isolation is not a consumer of either minimum chamber.

## 6. Chronological capacity and its unresolved branch

Tracked consumers give UE from unbounded exact-block hazard capacity in
the canonical reward box. Hence no Fin4 UE implies a finite uniform bound
on ∑[t,i]qᵢ(t) over all exact Nash–Bellman blocks in that box, independent
of their lengths. Every exact infinite spine in that box likewise has all
four marginal hazard sums finite.

For the normal class, a bounded spine with summable Bellman and root-regret
errors and at least one persistent player is also sufficient. A persistent
player means ∑[t]qᵢ(t)=∞. Neither such a spine nor unbounded capacity is
produced for arbitrary remaining tables.

The unresolved branch is bounded exact capacity. It permits arbitrarily
long blocks with tiny charge. Repetition needs source-matched continuation
values and error small relative to charge; absolute endpoint convergence
alone gives no such ratio.

A unilateral response transition and an exact predecessor transition are
different objects. A route using both must prove their matching; none of
the other conjecture-equivalent formulations requires that particular route.

## 7. Solved reward classes and finite recognition

Let Γᵢⱼ=rᵢ({j})−sᵢ, with recipients indexing rows and quitters columns.
The LCP at b asks for x≥0 with Γx+b≥0 and xᵢ(Γx+b)ᵢ=0 for all i.
Standard Q means solvability for every b; R0 means x=0 is the only solution
at b=0.

In addition to tracked low-cardinality, non-Q/homogeneous, punishment,
stationary, cyclic, and explicit-chamber consumers, the following complete
mathematical results supply sufficient criteria or quantitative constructions:

| Reward condition | Conclusion and boundary |
| --- | --- |
| Fin4: the whole reward table is equivariant under the regular Klein-four action | UE for arbitrary signed rewards, as a corollary of the implemented response-quotient criterion and elementary singleton branches. No nonsingleton inequalities beyond equivariance are required. |
| Fin4: the cyclic-child joint/solo raw family specified below, for every real R | UE, with an explicit fixed-target finite-law producer on the interval not covered by the singleton criteria. Both participants of the prescribed pair receive a positive collision premium; a full four-player premium core is allowed. This is an ordinary mathematical result awaiting formalization. |
| Fin4: the repeated-solo outsider-buffer family specified below, for every real R | UE allowing a positive outsider collision reward at the joint phase. A final solo exit supplies its continuation buffer. All rates and values are produced from rewards. This is a reviewed mathematical result awaiting formalization. |
| Fin4: the two-buffer joint/solo family specified below, for every real R | UE allowing all six outsider collision coordinates at the joint phase to be positive, under two weighted raw inequalities. Signed collision rewards and the zero-final-phase boundary are included. This is a reviewed mathematical result awaiting formalization. |
| Fin4: all tables in an open sixty-coordinate neighborhood of the explicit two-joint-phase rational table specified below | UE with rates and a fixed target produced from the table. Every singleton and collision reward may vary; only two solo phases require refinement. This is a reviewed mathematical result awaiting formalization. |
| Fin4: the global two-joint cyclic-child family specified below, for every real R | UE with simultaneous quitting at both retained joint phases. The rates and target are produced from rewards, including the outsider halfspace boundaries. This is reviewed mathematics awaiting formalization. |
| Fin4: the zero-premium joint-phase family specified below, for every real R and σ≥0 | UE with both joint participants at their singleton rewards and a possibly positive outsider collision payoff. Rates and a fixed target are produced; an opposite-sign pair core is allowed. This is reviewed mathematics awaiting formalization. |
| Fin4: nonnegative own singletons and participant premiums, with greatest premium core of size at most two | UE through full exact-root potential exclusion and reward closure. Players outside the core remain in the game and may have positive premiums. No strategic witnesses are assumed. This is an ordinary mathematical result awaiting formalization. |
| Fin4: nonnegative own singletons, greatest premium core {i,j}, and nonnegative product of the two pair join gaps | UE with arbitrary signed participant premiums. A degree argument selects a suitable exact root; it does not require every root to return. This is reviewed mathematics awaiting formalization. |
| Fin4: nonnegative own singletons, greatest premium core of size three, and all within-core joining differences nonnegative | UE with arbitrary signed participant premiums, including negative premiums inside the core and overlapping pair traps. A full triple-root index argument selects a suitable successor; weak comparisons use reward closure. This is reviewed mathematics awaiting formalization. |
| Fin4: nonnegative own singletons and a triple premium core with the mixed joining signs and two exact equalities specified below | UE with arbitrary signed participant premiums. The class allows negative within-core joining differences and is not covered by the joining-attractive criterion. It is an equality-stratum result, not a full reward-space neighborhood. This is reviewed mathematics awaiting formalization. |
| Fin4: nonnegative own singletons and a protected common leaver in every premium trap, as specified below | UE with arbitrary signed participant premiums for the other players. The criterion permits cores of size three or four and requires no strategic witness. Both strict and weak leave comparisons have production Lean consumers. |
| Fin4: nonnegative own singletons and a protected leaver for each premium trap, allowing different leavers for different traps | UE with signed premiums outside the protected set. The criterion is a finite test on rewards, not supplied strategic data. Both strict and weak leave comparisons have production Lean consumers. |
| Fin4: nonnegative own singletons and the weighted-floor/aggregate-leave tests specified below | UE even when every player has negative participant premiums somewhere. The weights are finite raw-table certificates; no root or strategy is assumed. Both strict and weak tests have production Lean consumers. |
| Fin4: nonnegative own singletons, premium traps of size three or four, and the boxed Nash-charge inequalities specified below | UE without a nonnegative weighted forced-Quit floor. Both trap sizes may coexist; every trap must pass its finite coefficient test. This is reviewed mathematics awaiting formalization. |
| Fin4: nonnegative own singletons, same-sign pair-trap joining gaps, and the boxed Nash-charge tests on every larger trap | UE for mixed pair and larger-trap configurations, including zero pair products by reward closure. The hypotheses force pair traps to be disjoint. This is reviewed mathematics awaiting formalization. |
| Fin4: det Γ<0 and Γ⁻¹≥0 entrywise | UE for every signed singleton level and nonsingleton completion. |
| Fin4: Γ is R0 and its integer LCP degree is not +1 | UE. Degree is the total Brouwer degree of x↦min(x,Γx+b), not a polynomial degree; no regularity premise is required. |
| Fin4: a stationary-response-invariant partition has quotient A that is R0 with degree not +1 | UE, including signed rewards. The partition condition is a finite system of linear identities in the raw table; the root is produced, not supplied. |
| Fin4: one ordered pair passes the sixteen weak lower/joining comparisons below | UE for arbitrary signed rewards, with no matrix condition. A finite outsider joining game produces the root; a negative sole-owner boundary uses the punishment consumer. |
| A guarded crossed stationary-response map has R0 linearization of degree not +1 | An exact stationary behavioral equilibrium with at least three positive hazards. Finite half-ceiling and full-ceiling raw tests produce such maps; weak half-ceiling tests give UE by reward approximation. |
| A triple S has Γ_SS invertible, Γ_SS⁻¹≥0, and Γ_kSΓ_SS⁻¹≥0 for each outsider k | UE with outsiders Never, for arbitrary nonsingleton rewards. |
| A proper child admits nonnegative domination weights satisfying the terminal, join, and Never inequalities | Its uniform payoff extends to the original game with complete outsider-deviation control. The weights satisfy an explicit finite raw-table linear test. |
| A proper child passes either the future-withdrawal or deadline-withdrawal inequalities below | Its fixed UE payoff extends with outsiders Never. The raw criteria are incomparable; deadline withdrawal also controls every nonincreasing nonnegative evaluation. |
| Uniform strict payoff deficit, nonconcentrated weighted payoff exclusion, or nonnegative-singleton weak subset exclusion | Actual finite profiles with arbitrarily small complete regret, hence a fixed UE payoff. |

Klein-four equivariance means rᵢ₊ₖ(S+k)=rᵢ(S) after identifying the players
with (ℤ/2ℤ)². In the branch with positive common own singleton,
positive total external-singleton surplus, and at least one external
singleton below the own singleton, the within-pair subgroup gives the
response quotient [[−A,B],[B,−A]] with B>A>0. Its negative determinant and
positive inverse activate the existing quotient consumer. A direct triangle
proof gives an alternative construction, not additional existence coverage.
Singleton symmetry alone is insufficient, and arbitrary
tables have no proved symmetry reduction.

The **cyclic-child joint/solo raw family** has parameters
a,b,c,h₁,h₂,h₃>0, abc>1, ξ,η>0, u≤1+ξ, v<1, q₂,q₃≤0,
and arbitrary real R. Its five prescribed reward vectors are

    r({0})=(1,−h₁,−h₂,−h₃),   r({1})=(u,0,b,−1),
    r({2})=(v,−1,0,c),         r({3})=(R,a,−1,0),
    r({0,1})=(1+ξ,η,q₂,q₃).

Write D=abc−1 and

    ν₁=(ac h₂+c h₁+h₃)/D,
    ν₂=(ab h₃+a h₂+h₁)/D,
    ν₃=(bc h₁+b h₃+h₂)/D.

The only additional restrictions are rₖ(A∪{k})≤0 for k∈{2,3} and
nonempty A⊆{0,1}: six outsider inequalities at the joint phase. Every
other reward coordinate is arbitrary. Define

    R_low=1+((1−u)ν₁+(1−v)ν₂)/ν₃,
    T_pass=max(1+ac(1−u)+a(1−v),
               1+((1−u)+ab(1−v))/b).

These thresholds satisfy R_low<T_pass. For R<R_low the singleton
matrix has degree zero; equality gives a positive homogeneous solution.
For R≥T_pass the passive inverse criterion applies, including equality.
The remaining interval R_low<R<T_pass is filled by a uniquely selected
admissible quadratic root and an intermediate-value argument producing
all four actual hazards. The quadratic may have either leading sign or
be linear; no strategic input or unresolved boundary case remains.

The constructed profile has one joint {0,1} phase and solo phases for
players 2 and 3. Subdividing only the solo phases preserves the target
exactly and makes their immediate-Quit errors vanish. Exact Continue
transport prevents error accumulation over a complete deviation. Geometric
opponent absorption gives uniform finite-horizon control; finite censoring
also gives actual finite laws with vanishing full regret. Positive
participant premiums at {2,3} are permitted, so these tables need not have
a premium core of size at most two.

Every table in this family fails product-low premiums. An explicit member
also escapes the proper-child F/J, homogeneous, nonunit-degree,
nonnegative-inverse, and nontrivial response-quotient criteria. These latter
separations concern that member, not every completion of the family.
The [complete raw-data theorem](exports/CYCLIC_CHILD_WITH_ONE_JOINT_PHASE.md)
supplies the rates and continuation values in the constructive interval and
the exact original-game criteria outside it. None is a strategic hypothesis.

The production source `CyclicChildJointPhase.exists_uniformPayoff`
(`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`)
derives the complete coarse certificate from the literal raw rows and caps
on its stated open pivot interval. The lower-endpoint equality has the
separate production consumer `CyclicChildJointPhase.exists_uniformPayoff_of_resonance`
(`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSingletonExits.lean`).
These declarations do not assert the complete all-R theorem above; the
remaining source exits and enlarged scalar selector are separate obligations.

The **repeated-solo outsider-buffer criterion** retains the four singleton
rows of the cyclic-child family, with u≤1, v<1, and prescribes

    r({0,1})=(1,η,−h₂,−h₃),   η>0.

Its only additional restrictions are

    r₂({0,2}), r₂({1,2}), r₂({0,1,2})≤0,
    r₃({0,3})≤λ,  r₃({1,3}), r₃({0,1,3})≤0,
    0≤λ<h₃η/h₁.

Every other reward coordinate is arbitrary, and R ranges over all real
numbers. Choose a scalar θ with λ≤h₃θ and 0<θ<η/h₁; this is a
finite reward inequality, not a strategic assumption. A scalar selector
produces a joint {0,1} phase followed by solo exits of players 2, 3,
and 0. The last phase gives outsider 3 a positive continuation value
at the joint phase. Subdivision of all three solo phases leaves the
target unchanged and controls every complete behavioral deviation.
Original-table singleton criteria cover the exterior R intervals.

The [complete repeated-solo theorem](exports/REPEATED_SOLO_EXIT_WITH_POSITIVE_OUTSIDER_BUFFER.md)
includes a full-core table outside the specified matrix, response-quotient,
common-leaver, and universal weighted child-debt criteria. This is a
separation from those criteria, not from every possible child strategy.

The **two-buffer joint/solo criterion** uses the same positive a,b,c,hᵢ,
abc>1, and ν above, but its prescribed rows are

    r({0})=(1,−h₁,−h₂,−h₃),   r({1})=(U,0,b,−1),
    r({2})=(V,−1,0,c),         r({3})=(R,a,−1,0),
    r({0,3})=(1+ξ,−h₁,−h₂,0),

where U,V≥1, ξ≥0, and R is arbitrary. Define

    R_low=1−((U−1)ν₁+(V−1)ν₂)/ν₃,
    J₁=max(0,r₁({0,1}),r₁({0,1,3})),  Q₁=r₁({1,3}),
    J₂=max(0,r₂({0,2}),r₂({0,2,3})),  Q₂=r₂({2,3}).

Require a scalar θ satisfying the finite reward conditions

    0≤θ<ν₂/h₁,                    ξ≥θ(1−R_low),
    (1+θ)J₁+ν₃Q₁≤ν₂−h₁θ,         (1+θ)J₂+ν₃Q₂≤θν₃.

No other reward entry is constrained; Q₁ and Q₂ may be negative.
For θ>0, all six outsider collision coordinates may instead be strictly
positive. A monotone scalar balance and an intermediate-value argument
produce a joint {0,3} phase followed by solo exits of players 1, 2,
and 3. When θ>0, both outsiders have positive continuation buffers at
the joint phase. Subdivision of every solo block preserves the fixed target;
opponent absorption controls unrestricted deviations and all large horizons.
The lower singleton-degree and upper passive-inverse exits cover the
remaining R values.

At θ=ξ=0 the last phase deletes literally. This includes the class with
three nonpositive player-2 collision rewards and J₁+ν₃Q₁≤ν₂, without
assuming openness of UE existence. A full-core example has premium traps
with empty common intersection. The two-buffer and repeated-solo criteria
cover different stated raw regions; no reduction of arbitrary tables to
their union is known.

The [complete two-buffer theorem](exports/TWO_OUTSIDER_BUFFERS_WITH_A_REPEATED_SOLO_EXIT.md)
contains the raw-data selector, original-table exterior cases, fixed-target
behavioral proof, and direct zero-phase specialization.

The **two-joint-phase neighborhood theorem** produces an open set in the
full sixty-coordinate reward space around an explicit rational table. Its
four macro phases are joint {0,3}, solo 1, solo 2, joint {0,3}.
An explicit two-equation elimination and nonsingular two-variable Jacobian
produce all six rates and every phase value for every nearby raw table.
The binding singleton floors remain identities; the other floors and all
joint-row outsider comparisons remain strict. Refining only the two solo
phases gives vanishing full behavioral regret at one unchanged target for
each table, with a uniform all-large-horizon bound.

The [complete neighborhood theorem](exports/TWO_JOINT_PHASES_FULL_TABLE_NEIGHBORHOOD.md)
specifies the full rational center and construction. It does not give a
numerical neighborhood radius or infer generic coverage from one open set.
The neighborhood can retain disjoint premium traps {0,3} and {1,2}, with
no weak leaver in {0,3}; the protected-leaver criteria therefore do not
cover it. The exact stationary exclusion at its center concerns player 3
kept quiet, not every stationary support or relabeling.

The **global two-joint cyclic-child criterion** has parameters
a,b,c,h₁,h₂,H>0, abc>1, U,V≥1, ξ,η>0, p₁≤a−h₁, p₂≤0,
and arbitrary real R. Prescribe

    r({0})=(1,−h₁,−h₂,−H),   r({1})=(U,0,b,−1),
    r({2})=(V,−1,0,c),       r({3})=(R,a,−1,0),
    r({0,3})=(1+ξ,p₁,p₂,η).

Its only additional restrictions are

    r₁({0,1}), r₁({1,3}), r₁({0,1,3})≤min(−h₁,p₁),
    r₂({0,2}), r₂({2,3}), r₂({0,2,3})≤0.

Every other reward coordinate is arbitrary. Define

    ν=(c h₁+ac h₂+H, h₁+a h₂+ab H, bc h₁+h₂+bH)/(abc−1),
    R_low=1−((U−1)ν₁+(V−1)ν₂)/ν₃,
    T=1−(c(U−1)+(V−1))/(bc).

The original-table singleton criteria give UE for R≤R_low and R≥T,
including equality. On the remaining interval a scalar selector produces
the four phases joint {0,3}, solo 1, solo 2, joint {0,3}. The selector
handles a missing zero of one continuation value and arbitrary η>0;
neither a favorable root nor a bounded collision premium is assumed.
Refining only the solo phases preserves one target and controls all
behavioral deviations and sufficiently long horizons. A joint-phase
outsider value may be negative; no all-phase singleton floor is required.

The [complete global two-joint theorem](exports/GLOBAL_TWO_JOINT_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md)
includes a full-core, no-pure-equilibrium example with disjoint pair traps.
It does not exclude all stationary producers or cover arbitrary tables.

The **zero-premium joint-phase family** prescribes, for any real R and σ≥0,

    r({0})=(1,−1,−1,−1),    r({1})=(2,0,2,−1),
    r({2})=(2,−1,0,2),      r({3})=(R,2,−1,0),
    r({0,3})=(1,σ,−1,0),

with only the additional caps

    r₁({0,1}), r₁({1,3}), r₁({0,1,3})≤1/2,
    r₂({0,2}), r₂({2,3}), r₂({0,2,3})≤0.

Every other nonsingleton coordinate is unrestricted. The singleton criteria
give original-table UE for R≤−1 and R≥1/4, including both equalities. On
the remaining interval, one scalar crossing selects a joint {0,3} phase
and two solo phases. Refining only the solos controls complete behavioral
deviations while retaining one target. The positive continuation buffer
permits the three player-1 collision caps to be positive even though both
joint participants receive zero singleton-relative premium.

The [complete zero-premium theorem](exports/ZERO_PREMIUM_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md)
includes an exact opposite-sign pair-core example outside the same-sign
pair criterion. It has no stationary equilibrium with a quiet player;
nonexistence of a fully supported stationary equilibrium is not asserted.
This is a raw reward family, not a normal form for arbitrary tables.

The **premium-core criterion** assumes sₖ≥0 and rₖ(S)≥sₖ for every
participant k∈S. A nonempty set A is a premium trap when every k∈A has
some S⊆A containing k with rₖ(S)>sₖ. Traps are closed under union;
their union C is the greatest premium core. Equivalently, repeatedly
remove any player whose participant rewards are all equal to its singleton
on the current subtable. Every removal order leaves the same C. This is
a finite calculation on rewards, not strategic deletion of players.

If |C|≤2, the original four-player game has UE. Passive rewards are
unrestricted. Players outside C may have positive premiums on coalitions
requiring other outside players. An empty core gives the existing
product-low criterion; a singleton core is impossible.

For a pair core, every positive exact root whose support differs from C
returns to the same lower singleton boundary through a flat active
participant. A strict pair-leaving preference rules out the exceptional
support there. Its return calculation needs a singleton floor only for the
designated leaving player's continuation coordinate. Positive outsider
hazards are treated before the two-core reduction, retaining simultaneous
quitting. With mutual strict joining, a possible exceptional mixed
root has local index −1, while the complete root map has total index +1;
after explicit tie removal, another exact root is produced. Boundary
minimization then excludes every smooth full-root potential. Equality in
a pair comparison is handled by reward closure of UE, not by claiming
closure of the stronger analytic exclusion.

The [complete theorem](exports/PREMIUM_CORE_AT_MOST_TWO.md) includes an
explicit layered-premium table outside the named product-low,
proper-child F/J, matrix, and response-quotient screens. Within the
nonnegative-singleton, nonnegative-participant-premium class, any
counterexample must therefore have |C|≥3. Negative participant premiums
remain outside this theorem; no reduction of arbitrary tables to its
hypotheses is known.

The **signed pair-core criterion** imposes no participant-premium lower
bound. With the same trap definition, assume C={i,j}, nonnegative own
singletons, and

    d_i = r_i({i,j}) - r_i({j}),
    d_j = r_j({i,j}) - r_j({i}),
    d_i d_j >= 0.

Then the original Fin4 game has UE. For strictly positive product, an
exact root whose successor is above every singleton must either be a pure
pair or the unique possible mixed pair. The pure pair gives a terminal
equilibrium. At a mixed bad root, all outsiders strictly Continue and the
full ambient local index is -1. Total index +1 therefore produces another
root with a low successor whenever the source has a below-singleton
coordinate. Minimizing the full-root potential on the boxed region with
some coordinate at or below its singleton gives a contradiction. Zero
join gaps are handled by perturbing passive rewards and applying UE reward
closure; no weak-gap analytic exclusion is asserted.

The [signed pair-core proof](exports/SIGNED_PAIR_CORE_SAME_SIGN_UNIFORM_EQUILIBRIUM.md)
permits negative participant premiums for every player. Its return is
existential: the same table can have a bad exact root as well. Opposite
strict join-gap signs admit a unique bad root of index +1 and are outside
this argument; that local regression is not a counterexample to UE.

The **joining-attractive triple-core criterion** assumes nonnegative own
singletons, greatest premium core C of size three, and the nine comparisons

    rᵢ(T∪{i})−rᵢ(T)≥0
    for i∈C and every nonempty T⊆C without i.

Participant premiums may have either sign, including inside C and on
coalitions involving outsiders. Pair traps inside C may overlap. With
strict comparisons, after the pure-core equilibrium exit every bad exact
root has pair or triple support with all active hazards proper. Its
active derivative has positive off-diagonal entries and zero diagonal. The triple local
index is therefore negative, as is the pair index. Simultaneous annotation
genericity treats ties of an inactive core player. The global index sum
forces a low-successor root, and compactness restores every original
below-singleton source. The same-domain minimum excludes the full-root
potential. Perturbing only passive within-core rewards preserves every
premium trap and supplies the weak boundary through UE reward closure.

The [complete triple-core theorem](exports/JOINING_ATTRACTIVE_TRIPLE_CORE_UNIFORM_EQUILIBRIUM.md)
includes signed and overlapping-trap fixtures outside the protected,
weighted-leave and boxed-charge hypotheses, and an actual bad triple root
that tests the existential, not universal, return conclusion. It does not
cover full cores or negative within-core joining differences. No reduction
of arbitrary tables to these raw hypotheses is asserted.

The **mixed-sign triple-core criterion** assumes nonnegative own singletons
and greatest premium core C={a,b,c}. With
d_i(T)=r_i(T∪{i})−r_i(T), its weak comparisons are

    d_a({b})≥0, d_b({a})≥0,
    d_a({c})≤0, d_c({a})≤0, d_b({c})≤0, d_c({b})≤0,
    d_a({b,c})=0, d_b({a,c})=0,
    d_c({a,b})≤0.

Participant premiums may have either sign. Every table satisfying these
raw conditions has an original-game UE payoff against all unilateral
behavioral deviations. In the strict-sign case, a bad root with a sure
quitter either gives the pure-{a,b} equilibrium exit or is impossible.
Every remaining bad pair or triple root has full ambient local index −1.
After avoiding inactive-core ties, total index +1 produces an exact root
whose successor is at or below a singleton. Compactness restores arbitrary
sources, and the full-root potential consumer gives UE. Passive reward
perturbation supplies the weak signs while preserving both equalities
and the premium core.

The [complete mixed-sign theorem](exports/MIXED_SIGN_TRIPLE_PREMIUM_CORE_UNIFORM_EQUILIBRIUM.md)
includes a rational table beyond the compared implemented and accepted raw
criteria, including joining-attractive triple cores. It therefore removes
an additional reward-table class from possible UE counterexamples. The two
equalities are part of the criterion: relaxing one admits a positive-index
bad-root regression. That regression refutes the proposed index extension,
not UE. No full-core or unrestricted three-core theorem is asserted.

The **protected common-leaver criterion** uses the same positive-premium
trap definition even when participant premiums have either sign. It assumes
nonnegative own singleton rewards and a player p such that:

- rₚ(S)≥sₚ for every coalition S containing p;
- every premium trap contains p; and
- rₚ(T∪{p})≤rₚ(T) for every nonempty T⊆C\{p}.

No participant-premium sign is imposed on any other player. These are finite
tests on the reward table. They imply UE for the original four-player game;
there is no deletion of p or assumed equilibrium of a child game.

For strict leave comparisons, every absorbing exact root whose continuation
satisfies vₚ≥sₚ returns to the compact domain

    D={v∈[−B,B]⁴ : vₚ≥sₚ and some vᵢ≤sᵢ},

where B exceeds a reward bound M. A root supported on a trap would make its
active player p strictly prefer Continue. Any other support has an active
player with every participant reward at most its singleton, so the successor
belongs to D. Unlike the nonnegative-premium case, it may lie below a
singleton floor.

A full-root potential's minimum on D must first lie on the singleton lower
boundary. The singleton-face derivative inequalities then give two binding
coordinates. Lowering a binding coordinate k≠p by ε preserves p's floor;
every exact root returns to the same D and has absorption at least
ε/(3M+B). This contradicts minimality and the directional derivative.
The existing Fin4 polynomial-obstruction theorem yields UE; weak leave
comparisons follow by perturbing only passive rewards and applying reward
closure. No weak-comparison analytic potential exclusion is asserted.

The production declarations are
`exists_uniformEquilibriumPayoff_of_commonLeaver_strictLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/CommonQuittingPremiumLeaverUniformPayoff.lean`)
and `exists_uniformEquilibriumPayoff_of_commonLeaver_weakLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/CommonQuittingPremiumLeaverRewardClosure.lean`).
They supply the raw-table-to-UE conclusion, not merely the return-domain
criterion. Their pair-core specializations still require a leave comparison;
they do not implement the separate mutual strict-join branch of the
core-at-most-two theorem.

The [complete proof and exact boundary tests](exports/COMMON_LEAVER_WITH_SIGNED_PREMIUMS.md)
include a three-player core with a genuinely negative participant premium.
The criterion does not cover traps with no common member, negative participant premiums of every
possible protected member, or failed leave comparisons for all such members.
It is not a normal form for arbitrary reward tables.

The **support-specific protected-leaver criterion** removes the requirement
that one player work for every trap. Define directly from the table

    P={i : rᵢ(S)≥sᵢ for every coalition S containing i}.

Assume every premium trap A has some p∈A∩P with

    rₚ(T∪{p})≤rₚ(T) for every nonempty T⊆A\{p}.

With nonnegative own singletons this implies UE. All participant rewards
outside P may be signed. Strict comparisons exclude smooth full-root
potentials for any finite player set; weak comparisons yield the Fin4
strategic theorem by reward closure. The proof minimizes on one fixed
protected-floor domain. When every binding coordinate is protected, it
uses the closed Nash graph at that actual minimum and an error negligible
relative to absorption, not an unjustified return from a perturbed source.

The [complete protected-set theorem](exports/SUPPORT_SPECIFIC_LEAVERS_WITH_SIGNED_PREMIUMS.md)
contains a proper-three-player-core example requiring different protected
leavers and having a negative participant premium. Its full-core case is
already covered by the globally safe quiet-player composition below.
The production declarations are
`exists_uniformEquilibriumPayoff_of_supportSpecific_strictLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/SupportSpecificQuittingPremiumLeaversUniformPayoff.lean`)
and `exists_uniformEquilibriumPayoff_of_supportSpecific_weakLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/SupportSpecificQuittingPremiumLeaversRewardClosure.lean`).
They also allow an empty protected set when there are no traps. The criterion
does not cover a trap with no suitable protected leaver. No reduction of
arbitrary tables to this criterion is asserted.

The **weighted-floor/aggregate-leave criterion** does not require an
individually protected player.
For each premium trap A, choose weights lambda^A strictly positive on A
and zero outside A. Require the same weights to satisfy both tests:

    W_A(S) = sum_i lambda_i^A [r_i(S union {i}) - s_i] >= 0
             for every S contained in I, including coalitions outside A;
    L_A(T) = sum_{i in A minus T} lambda_i^A [r_i(T union {i}) - r_i(T)] <= 0
             for every nonempty proper T contained in A.

With nonnegative own singletons these finite linear feasibility conditions
imply Fin4 UE. The first test makes every exact Nash successor satisfy the
corresponding weighted singleton floor. Strict versions of the second test
exclude trap supports at sources satisfying those floors. Minimize a putative
potential over points of that convex domain with some coordinate at or below
its singleton. A vanishing-absorption perturbation at this actual minimum
contradicts the full-root drift inequality. Weak
leave follows by increasing passive rewards and applying reward closure.

The [complete weighted-floor theorem](exports/WEIGHTED_FLOOR_RETURN_UNIFORM_EQUILIBRIUM.md)
includes an open sixty-coordinate reward region with no individually
protected player. It fails the implemented supportwise nonpositive-premium
test: all members of one triple have strictly positive participant premiums
at that triple. The aggregate argument excludes unsuitable Nash supports, rather
than imposing a low participant payoff at every product root.
The production declarations are
`exists_uniformEquilibriumPayoff_of_weightedTrap_strictLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversUniformPayoff.lean`)
and `exists_uniformEquilibriumPayoff_of_weightedTrap_weakLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversRewardClosure.lean`).
Both take only nonnegative own singletons and the corresponding finite raw
weight tests; the weak conclusion uses reward closure, not a weak analytic
potential exclusion.
The weighted and protected-leaver raw criteria are incomparable. Neither
their union nor these criteria together with the periodic constructions
are known to cover all remaining tables.

The **boxed Nash-charge criterion** assumes nonnegative own singletons
and that every premium trap has size three or four. Put M=max|rᵢ(S)|.
For each trap A, let m=|A| and, for ∅≠T⊊A, define

    P_A(T)=∑[i∈A\T] (rᵢ(T∪{i})−sᵢ),
    L_A(T)=∑[i∈A\T] (rᵢ(T∪{i})−rᵢ(T)).

Require positive d,τ,g,ℓ, possibly different for each trap, with

    |T|=1:        P_A(T)≤−d,  L_A(T)≤−g,
    2≤|T|≤m−2:   P_A(T)≤0,   L_A(T)≤0,
    |T|=m−1:      P_A(T)≤τ,   L_A(T)≤−ℓ,
    C_A=m(d/τ)^(1/(m−2))(g+ℓd/τ)>∑[i∈A]sᵢ+mM.

The intermediate range is empty for triples. Explicitly,

    C₃=3(d/τ)(g+ℓd/τ),    C₄=4√(d/τ)(g+ℓd/τ).

These finite reward inequalities imply UE. The strict margins choose one
common box bound B>M for all traps. A trapped exact root whose active Quit
endpoints all exceed their singletons has only interior hazards. Their odds
have sum U and degree-(m−1) symmetric sum E satisfying dU<τE and
E≤U^(m−1)/m^(m−2). The aggregate Nash identity then forces

    ∑[i∈A](sᵢ−vᵢ)>C_A,

contradicting the source box. Nontrap supports already have a low active
endpoint. Thus every absorbing exact root in this box has a low successor,
which excludes a smooth full-root potential and activates the Fin4 consumer.

The [complete boxed-charge theorem and exact tests](exports/BOXED_NASH_CHARGES_UNIFORM_EQUILIBRIUM.md)
include triple and full-core examples for which every nonzero nonnegative
linear forced-Quit-floor test fails. The full-core example also supplies a
profitable omitted player for an exact equilibrium witness in every proper
child. Exact high-successor roots outside the box show why its bounded-source
premise is essential. Pair traps are outside this criterion. Neither the
signed-pair nor the boxed-charge criterion is an exhaustive classification
of the remaining reward tables.

The **mixed premium-trap criterion** allows pair traps and larger traps in
the same table. Own singletons are nonnegative. For every pair trap {i,j},
require

    (rᵢ({i,j})−rᵢ({j})) (rⱼ({i,j})−rⱼ({i}))≥0.

Every larger trap satisfies the boxed Nash-charge tests above, with its own
positive constants. These conditions force the pair traps to be disjoint:
overlapping traps {i,j} and {i,k} would make {i,j,k} a trap whose singleton
P coefficient at {i} is positive, contradicting its negative bound. Fin4
therefore allows at most two such pairs.

Larger-support charges exclude their all-high successors in one common
box. At a generic below-singleton source, all remaining bad exact roots
have pair support and local ambient index −1. The full root relation has
total index +1, so a suitable low-successor root exists. Compactness restores
every below-singleton source, and the same-domain minimum argument excludes
the polynomial obstruction. Passive reward perturbations handle zero pair
products without changing participant data or the trap list.

The [complete mixed-trap theorem](exports/MIXED_PREMIUM_TRAPS_UNIFORM_EQUILIBRIUM.md)
includes a full-core table with two pair traps, no pure equilibrium, no
nonzero nonnegative forced-Quit floor, and a profitable omitted player at
an exact Nash witness in every proper child. Its reward criterion lies
outside both the pair-core and pair-free boxed criteria. It does not cover
opposite-strict-sign pair gaps or larger traps failing the charge tests,
and it supplies no exhaustive classification of arbitrary tables.

For the child criterion, choose a nonempty proper S⊂I. For each outsider k,
the conditions on weights λₖᵢ≥0, i∈S, are

    sₖ≤∑[i∈S]λₖᵢsᵢ,
    sₖ−rₖ(A)≤∑[i∈S]λₖᵢ(sᵢ−rᵢ(A)),
    rₖ(A∪{k})−rₖ(A)≤∑[i∈S]λₖᵢ(rᵢ(A∪{i})−rᵢ(A)),

with the last two required for every nonempty A⊆S. The first inequality
may be omitted if some child own singleton is positive. In Fin4, a child
of size three has UE unconditionally; no child strategy is an extra input.

For existence, rather than extension of a specified child target, a
nonnegative child singleton suffices whenever 1≤|S|≤3. The child-law
selection, finite quiet lift, and one fixed target are tracked. Raise that
singleton by δ>0 and
select a δ²-Nash profile in the perturbed child. Its joint-Never probability
is at most δ; restoring the original rewards gives child regret at most
δ+δ². The original future/join debt bounds then produce parent regret
tending to zero with every outsider literally Never. Finite censoring and
payoff subsequence selection retain finite quiet witnesses at one fixed
target. The same argument applies to all five withdrawal certificate kinds.
The existence conclusion also follows by reward closure of the positive
class; the explicit selected-family statement retains vanishing joint Never.
It does not preserve every prescribed child target or make the raw tests
exhaustive. In the single-pivot normalization, it permits the zero-singleton
child {1,2,3} whenever the omitted pivot satisfies the future/join inequalities.

Two additional finite child tests allow withdrawals. For each outsider k,
one fixed pair of weight vectors must satisfy all its rows simultaneously
for every nonempty A⊆S. Put

    ℓᵢ=min({0}∪{rᵢ(B): ∅≠B⊆S∖{i}}),
    aᵢ=max(0,sᵢ),
    cᵢ=min({aᵢ}∪{rᵢ(B): ∅≠B⊆S∖{i}}).

Define Wᵢ(A)=0 if i∉A, Wᵢ({i})=ℓᵢ−sᵢ, and
Wᵢ(A)=rᵢ(A∖{i})−rᵢ(A) for i∈A with |A|≥2. Define Lᵢ(A) by the same
formula with cᵢ in place of ℓᵢ. The future-withdrawal test asks for λᵢ,μᵢ≥0
with

    sₖ≤∑ᵢλᵢsᵢ+∑ᵢμᵢaᵢ,
    sₖ−rₖ(A)≤∑ᵢλᵢ(sᵢ−rᵢ(A))+∑ᵢμᵢLᵢ(A),
    rₖ(A∪{k})−rₖ(A)≤∑ᵢλᵢ[rᵢ(A∪{i})−rᵢ(A)]+∑ᵢμᵢLᵢ(A).

It gives terminal outsider debt at most ∑ᵢ(λᵢ+μᵢ)dᵢ of the child.
The patient replacement behind cᵢ uses actual increasingly late finite
clocks when sᵢ≥0; its terminal bound is not a finite-horizon or discounted
bound on the same profile.

The deadline-withdrawal test asks for uᵢ,vᵢ≥0 with

    sₖ≤∑ᵢuᵢsᵢ,
    sₖ−rₖ(A)≤∑ᵢuᵢ(sᵢ−rᵢ(A)),
    rₖ(A∪{k})−rₖ(A)≤∑[i∉A]uᵢ[rᵢ(A∪{i})−rᵢ(A)]
                         +∑[i∈A]vᵢWᵢ(A).

It gives outsider debt at most ∑ᵢmax(uᵢ,vᵢ)dᵢ for terminal evaluation
and every nonnegative nonincreasing evaluation with Never weight zero.
The maximum coefficient comes from disjoint private-clock events, not
public correlation. For either test, the Never inequality can be omitted
for terminal quiet extension if some child sⱼ>0. The displayed debt bound
then acquires eₖdⱼ/sⱼ, where eₖ is the positive part of the omitted
Never-row deficit; the extension conclusion is unchanged.

The deadline floor can be improved by a finite security program. Let Vᵢ
be the maximum v over 0≤h≤1 satisfying

    v≤sᵢ,     v≤(1−h)rᵢ(B)+h rᵢ(B∪{i})
               for every ∅≠B⊆S∖{i}.

Replacing ℓᵢ by max(ℓᵢ,Vᵢ) is valid for the terminal test. For the
all-evaluation test use min(max(ℓᵢ,Vᵢ),0). A positive value attained only
at h=0 is approached by positive clocks, not assigned to Never.
Each test must hold separately for every outsider, with sums over i∈S.
In Fin4 all proper children have UE, so these are raw-table producers,
not supplied-strategy criteria. None of the child tests is known to be
exhaustive.

For the last row, write V(r) for the set of attainable prescribed payoff
vectors. The respective conditions are

    ∃κ>0, ∀u∈V(r), minᵢ(uᵢ−sᵢ)≤−κ;

    ∃β<1, ∀u∈V(r), ∃w≥0:
        ∑ᵢwᵢ=1, maxᵢwᵢ≤β, w·(u−s)≤0;

    ∃nonempty J with sᵢ≥0 on J:
        ∀u∈V(r), ∃i∈J, uᵢ≤sᵢ.

For signed Fin4 tables, the weaker condition
∀u∈V(r), ∃i∈I, uᵢ≤sᵢ already implies qualitative UE by the tracked strict
minimum-payoff isolation theorem. It does not supply the signed-owner
quantitative selector asserted under the third condition.

Uniform strict deficit with all sᵢ≥0 also yields one profile that is exact
terminal Nash at every literal suffix and uniform at its initial payoff.
Strict deficit with signed singletons alone need not attain terminal Nash.

The finite selection mechanisms have tracked implementations; the additional
raw-table recognition follows from the mathematical payoff-compression result:
V(r) is exactly the image of independent laws on the common calendar
{0,…,19,Never}, with at most five positive-support actions per marginal,
counting Never. It is compact.

Writing Aᵢ=Uᵢ−sᵢ for a calendar law, the three raw tests are equivalently:

- P: no calendar law has Aᵢ≥0 for every i.
- G: one λ∈(0,1/2] works for every calendar law, each of which has distinct
  i,j satisfying (1−λ)Aᵢ+λAⱼ≤0.
- W_J: sᵢ≥0 on the fixed nonempty J, and no calendar law has Aᵢ>0 for all i∈J.

These are finite real-algebraic predicates of the reward table, decidable
for rational or encoded algebraic rewards. They are sufficient, not exhaustive.
This compresses prescribed payoffs, not unrestricted caps or exploitability;
the produced approximate equilibria need not have twenty dates.

Further explicit periodic/stationary reward families have complete consumers,
including a paired-collision family for every value of its real parameter.
They do not cover arbitrary completions of their singleton matrix.

The integer-degree restriction leaves degree +1 matrices, still subject to
other sufficient classes. The quotient condition can exclude tables even
when the full matrix has degree +1. Precisely, for stationary hazards q put

    Δᵢ(q)=(1−αᵢ(q))Qᵢ(q)−Hᵢ(q),

where αᵢ is opponent survival, Qᵢ is the Quit-now payoff, and
Hᵢ=∑[∅≠T⊆I\{i}]Pr_q(opponent Quit set=T)rᵢ(T) is an unnormalized
one-stage contribution. The stationary Never value is Hᵢ/(1−αᵢ) when
αᵢ<1, and zero when αᵢ=1.
For a partition O₁,…,Oₖ let Ex repeat xₐ on every player in Oₐ. The condition is
Δᵢ(Ex)=Δⱼ(Ex) for every x∈[0,1]ᵏ whenever i,j share a block. Its quotient is

    Aₐᵦ=∑[j∈Oᵦ]Γᵢⱼ,       i∈Oₐ,

independent of the chosen i. The quotient uses sums, not averages; block
players still randomize independently and are not merged into one agent.
Every hypothetical counterexample must have R0, degree +1 quotients for
every such partition. An immediate sufficient Fin4 test is det A<0 and
A⁻¹≥0; no separate R0 input is needed for that test.

For example, take Γ with within-pair entries 3 on {0,1} and {2,3}, cross-pair
entries −1, and zero diagonal. Impose only
r₁((0 1)S)−s₁=r₀(S)−s₀ for every nonempty S. Every such table has UE,
allowing 33 independent nonsingleton entries and arbitrary signed own-singleton levels. The full Γ
has degree +1, while the {0,1},{2},{3} quotient has degree −1.

There are also sufficient conditions without response-row identities.
For an ordered pair (a,b), put J=I∖{a,b}. Just the sixteen weak comparisons

    min[T⊆J]rₐ(T∪{a}) ≥ max[∅≠T⊆J]rₐ(T),
    rᵦ(T∪{a,b})≤rᵦ(T∪{a})             for every T⊆J

imply signed Fin4 UE, with no determinant or inverse hypothesis. Prescribe
a surely Quit and b Never, and solve the outsiders' finite joining game.
A nonzero outsider hazard gives a stationary behavioral equilibrium. If
both outsiders Continue, every other player has no profitable join. The
negative-own-singleton case is then consumed using the contrary-source
punishment bound; it is not asserted to give a stationary equilibrium.
Every hypothetical Fin4 counterexample must fail this test for every
ordered pair.

For the stronger interior stationary construction let P swap coordinates
a,b and choose h∈(0,1]. Require Γₐᵦ,Γᵦₐ>0 and, for each selected i with
partner j,

    Δᵢ(qⱼ=0,z)>0 for every nonzero z∈[0,1]ᴶ,
    Δᵢ(qⱼ=h,z)<0 for every z∈[0,1]ᴶ.

If PΓ is R0 with degree not +1, the crossed clipping map produces an
original-game stationary equilibrium with 0<qₐ,qᵦ<h and at least one
positive outsider hazard. All deleted opponent clocks contract, including
for signed rewards. The nonzero fixed-point set has total modified-map
degree 1−degree(PΓ); this is not a count of equilibria.

An explicit finite strict test is det Γ>0, Γ⁻¹>0 and both selected lower
rankings above strict, together with either both full-ceiling joining
comparisons strict, or eighteen strictly negative degree-(2,2) Bernstein
coefficients of Δₐ,Δᵦ at partner hazard 1/2. In the latter case h=1/2.
Retaining det Γ>0, Γ⁻¹≥0, weak lower rankings and nonpositive half-ceiling
coefficients still give UE, but exact stationary attainment is not claimed.
The full-ceiling qualitative Fin4 conclusion is already covered by the
simpler sixteen-comparison theorem. The half-ceiling class is not: it can
allow profitable joins at partner hazard one. The half-ceiling example
fails the sixteen-comparison test for every ordered pair. Both ceiling
examples have no nontrivial response-invariant partition. The half-ceiling
example fails every basic capped-clock proper-child test; the full-ceiling
example fails all four three-player-child tests. No guard or passing pair
is produced for an arbitrary remaining table.

Standard Q alone is not an existence theorem.
Neither a fixed small periodic class nor the proper-child extension tests
are known to cover all remaining tables.

## 8. Exact negative search

A tracked Research semidecision enumerates normalized rational reward tables,
positive rational scales, and finite lower certificates. Some finite stage
succeeds iff some real Fin4 table has η>0. Every fixed unit-bounded rational
positive-gap table has a finite successful stage. An arbitrary rational
positive-gap table can first be positively scaled into that class.

Each accepted lower certificate covers every behavioral profile. A grid
failure for stationary or finite-menu strategies is not such a certificate.
Nontermination has no conclusion. Completeness of the theoretical dovetail
does not assert that a particular practical search implements its whole
schedule or has a useful runtime bound.

No accepted positive-gap table is known. A positive resolution may exclude
the certificate language universally; a negative resolution must supply
one accepted instance or an equivalent unrestricted proof.

## 9. Remaining decisive obligations

| Route | What remains to be proved |
| --- | --- |
| Finite laws | Select the three independent nonpivot laws with inner repair value tending to zero. |
| Maximum-regret sources | Consume either the generic singleton-bearing source or the single-pivot source with strict pressure and a singleton-removing delay, controlling the changed nonmover caps. |
| Total-debt source | Consume full-debt, reset-rigid, and off-minimum paid configurations, including all exits of any proposed rank. |
| Forward play | Produce the bounded absorption-relative packets or the punishment-vector sure root from the remaining table. |
| Global obstruction | Exclude every full robust polynomial/positive invariant barrier, or construct one for an explicit table. |
| Matrix classification | Consume tables surviving full and quotient degree tests, guarded crossed-response tests, and the matrix-free oriented-pair test, using actual all-behavior realization. |

These are alternative routes, not successive mandatory steps. There is no
proved finite exhaustive state machine with all nonterminal cycles consumed.

For arbitrary finite player counts, a cardinal reduction or an arbitrary-player
producer remains necessary. Existing passive padding transports counterexamples
upward, not from larger games down to Fin4. The reverse implication from
arbitrary absorbing row-perfect witnesses to approximate equilibrium is a
separate general-player problem. The tracked forward AKRS/S.3 construction
does not produce its own approximate-equilibrium premise. Finite quitting
games are not a proved normal form for all finite stochastic games.

## Tracked source anchors

- Terminal endpoint:
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`);
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  (`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`).
- Reward and strategy reductions:
  `exists_finFour_no_uniformPayoff_iff_exists_singlePivot`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`);
  `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close`
  (`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`);
  `exists_finiteDeadlineTimingProfile_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`).
- Finite-law values:
  `singlePivot_fullExploitability_eq_max_menuExploitability_scalar`
  (`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`);
  `exists_objective_minimizer_eq_behavioral_infimum`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`);
  `smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairUniformPayoffCharacterization.lean`).
- Selected low-player laws:
  `exists_terminalProfile_smallExploitability_smallNever_of_nonnegativeSingleton`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/NonnegativeSingletonEarlyAbsorption.lean`);
  `exists_uniformFiniteQuietFamily_of_withdrawalFutureJoinFamily`
  (`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFiniteQuietSource.lean`).
- Complete forward/polynomial alternatives:
  `quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot`
  (`UniformEquilibrium/Quitting/Projective/FixedBoxForwardCharacterization.lean`);
  `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`);
  `exists_finFour_no_uniformPayoff_iff_exists_boundedSinglePivotPolynomialObstruction`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourBoundedSinglePivotPolynomialObstruction.lean`).
- Compact barrier:
  `nonempty_closedInvariantBarrier_iff_le_controllerTesterValue`
  (`UniformEquilibrium/Quitting/ControllerTester/BarrierDuality.lean`).
- The two minima:
  `minimumTerminalSemantic_maximumDebt_allPlayersTie`
  (`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`);
  `finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`).
- Capacity:
  `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`);
  `all_marginalQuitHazards_summable_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardNashBellmanSpine.lean`).
- Finite cap-threshold descent and minimum isolation:
  `exists_literal_capThreshold_block_debtSum_le_quadraticDrop`
  (`UniformEquilibrium/Quitting/Paths/FiniteSoloCapThresholdDescent.lean`);
  `positive_minimum_fourPlayer_allOwner_quadraticMargins`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`);
  `exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`).
- Exact negative search:
  `exists_finFourCounterexampleStep_iff_exists_real_infimum_pos`
  (`Research/Quitting/FinFourCounterexampleSemidecision.lean`).
