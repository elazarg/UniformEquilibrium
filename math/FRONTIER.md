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
| Fin4: the joint/solo raw family specified below | One fixed UE target and actual finite laws with vanishing full regret. Both participants of the prescribed pair receive a positive collision premium. This is an ordinary mathematical result awaiting formalization. |
| Fin4: nonnegative own singletons and participant premiums, constant participant rewards outside a pair, and one member strictly prefers the other's singleton to the pair | UE by exclusion of every smooth full exact-root potential. No outsider joining inequalities or strategic witnesses are assumed. This is an ordinary mathematical result awaiting formalization. |
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

The **joint/solo raw family** has parameters a,b,c,h₁,h₂,h₃>0, abc>1,
u,v<1, ξ,η>0 and q₂,q₃≤0. Its five prescribed reward vectors are

    r({0})=(1,−h₁,−h₂,−h₃),   r({1})=(u,0,b,−1),
    r({2})=(v,−1,0,c),         r({3})=(R,a,−1,0),
    r({0,1})=(1+ξ,η,q₂,q₃).

Write D=abc−1 and

    ν₁=(ac h₂+c h₁+h₃)/D,
    ν₂=(ab h₃+a h₂+h₁)/D,
    ν₃=(bc h₁+b h₃+h₂)/D.

The required interval, always nonempty, is

    1+((1−u)ν₁+(1−v)ν₂)/ν₃ < R < 1+ac(1−u)+a(1−v).

The only additional restrictions are rₖ(A∪{k})≤0 for k∈{2,3} and
nonempty A⊆{0,1}: six outsider inequalities at the joint phase. Every
other reward coordinate is arbitrary. The construction selects one joint
{0,1} phase and solo phases for players 2 and 3. Subdividing only the solo
phases preserves the target exactly and makes their immediate-Quit errors
vanish. Exact Continue transport prevents those errors from accumulating
over a complete deviation. Finite censoring retains the target and full
regret bounds. If every other participant reward is at most its own
singleton, the coarse three-phase profile is already exact terminal Nash.

Every table in this family fails product-low premiums. An explicit member
also escapes the proper-child F/J, homogeneous, nonunit-degree,
nonnegative-inverse, and nontrivial response-quotient criteria. These latter
separations concern that member, not every completion of the family.
The [complete raw-data producer](exports/ONE_JOINT_PHASE_WITH_DIFFUSE_SOLO_EXITS.md)
supplies the rates and continuation values; none is a strategic hypothesis.

The **two-player premium-core criterion** requires a pair {i,j} with

    rₖ(S)≥sₖ for every k∈S,
    rₖ(S)=sₖ for every k∈S outside {i,j},
    rᵢ({i,j})<rᵢ({j}).

Nonparticipant rewards and the two core players' nonnegative premiums on
larger coalitions are unrestricted. For any finite player set, even with
signed singletons, these conditions exclude every C¹ function H satisfying

    H(v)−H(T_q(v))≥a(q)

on all exact Nash-root edges in any box [−B,B]ᴵ strictly containing the
rewards. The proof minimizes H on the singleton lower boundary and lowers
only binding constant-participant coordinates; every resulting exact root
returns to that same boundary with a quantitative positive absorption.
For Fin4 with s≥0, the existing no-UE polynomial producer supplies exactly
such a potential, so its exclusion proves UE. The
[complete theorem](exports/TWO_PLAYER_PREMIUM_CORE_STRICT_LEAVE.md) includes
an explicit table outside the named product-low, proper-child F/J, matrix,
and response-quotient screens. No reduction of arbitrary tables to this
premium pattern is known.

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
