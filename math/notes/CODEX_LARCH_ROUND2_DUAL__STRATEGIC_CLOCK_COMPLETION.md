# Completion and compactness of finite-feature clock geometry

Author: CODEX_LARCH_DUAL.

Status: ordinary mathematical proof sketch, passed
[independent review by CODEX_LARCH](../feedback/CODEX_LARCH_ROUND2_DUAL__STRATEGIC_CLOCK_COMPLETION__BY_CODEX_LARCH.md)
with no unresolved mathematical objection; not Lean-checked or exported.
This extends the independently reviewed
[clock seminorm](CODEX_LARCH_ROUND2_DUAL__STRATEGIC_CLOCK_SEMINORM.md)
by classifying its completion and totally bounded families. The object is
generic random-time observability; no new equilibrium construction is sought.

**Main result:** one nonzero cumulative-mass coefficient gives the ordinary
TV topology and no additional completion points. When every cumulative
coefficient vanishes, the geometry reduces to atom-supremum distance plus
possibly observed Never mass. If BOTH atom size and Never mass are observed,
one additional scalar records diffuse finite mass lost in the limit. This is
the only incomplete case, modulo null directions.

## 1. Generic finite-feature model

Let p be a probability law on ℕ∪{∞}. Write x_t=p(t) and ν=p(∞), so
x≥0, Σ_t x_t+ν=1. For finitely many observers h and marks S, fix real
coefficients s_h,a_hS,b_hS. There may be no marks for an observer. The metric
from before/tie/after tests has the form

    d(p,q)=max {
       max_h |s_h(ν_p−ν_q)|,
       sup_(t,h,S) |a_hS F_(p−q)(t−)+b_hS(p(t)−q(t))|
    },                                                   (1)

where F_(p−q)(t−)=Σ_(k<t)(p(k)−q(k)). Empty maxima are zero.
The earlier note proves the quitting-game specialization and the
all-observer extension. Here the coefficients themselves are the data.
This also covers a generic finite collection of bounded time-order tests.

Put

    a_* = max_(h,S)|a_hS|,
    c = max_h|s_h|,
    β = max_(h,S)|b_hS|.

The scalar distinction a_*>0 versus a_*=0 determines the topology. In the
second case only the two numbers c and β remain relevant. A common finite
coefficient bound gives d≤C·TV for some C; for literal reward tests bounded
by M one may take C=2M.

## 2. Classification table

All completeness assertions below are after quotienting by d=0.

| Coefficients | Intrinsic geometry | Completion | Total boundedness of family D |
|---|---|---|---|
| a_*>0 | Same topology as TV; metric separates laws | Actual law space is complete | Uniformly small late finite TOTAL mass |
| a_*=0, β>0, c=0 | β times the supremum norm of finite atoms | Actual law space is complete | Uniformly small late ATOMS |
| a_*=0, β>0, c>0 | Atom supremum plus Never-mass distance | Extra diffuse-mass scalar needed | Uniformly small late ATOMS |
| a_*=0, β=0, c>0 | Only Never mass is observed | Compact interval [0,1] | Every family |
| a_*=0, β=0, c=0 | All laws are identified | One point | Every family |

The two tail conditions mean respectively

    lim_(N→∞) sup_(p∈D) Σ_(t≥N) p(t)=0,                 (2)
    lim_(N→∞) sup_(p∈D,t≥N) p(t)=0.                     (3)

Neither condition includes the Never mass. They must not be confused with
proper TV approximation, whose tail also includes Never.

## 3. A cumulative coefficient prevents lost mass

Assume one test has a≠0 and coefficient b. Its values on p−q are

    e_t=aF_(p−q)(t−)+b(p(t)−q(t)).

First, d convergence determines every finite atom. If b≠0, start from
F(0−)=0 and recover the atom differences recursively from e_t. Each fixed
coordinate depends on only finitely many test values. If b=0, e_t/a directly
gives the cumulative differences and hence consecutive atom differences.
Also, sending t to infinity gives

    |a|·|ν_p−ν_q|≤d(p,q).                               (4)

Thus d convergence to an actual law gives convergence at every atom,
including Never. Pointwise convergence of normalized probability masses on
this countable set implies TV convergence: retain a finite set carrying all
but ε of the limiting mass, control its finitely many coordinates, and bound
both complementary masses. Together with d≤C·TV, this proves equality of
the two topologies.

### Completeness needs a separate argument

Let p_n be d-Cauchy. The recurrence gives coordinate limits x_t≥0, and (4)
gives ν_n→ν. Finite partial sums show Σ_t x_t≤1−ν. It remains to rule out
missing finite mass.

Given ε>0, choose n,m sufficiently large that d(p_n,p_m)≤ε. Hold n fixed
and let m tend to infinity in each finite-date test. Then

    |a(F_pn(t−)−Σ_(k<t)x_k)+b(p_n(t)−x_t)|≤ε.

The limiting x sequence is summable by the partial-sum bound, so x_t→0.
Sending t to infinity now gives

    |a|·|(1−ν_n)−Σ_t x_t|≤ε.

Then let n tend to infinity and ε decrease to zero. It follows that
Σ_t x_t=1−ν, so p=(x,ν) is an actual probability law. The preceding finite-
set argument gives p_n→p in TV, hence in d. There are no additional points
in the metric completion.

### Compactness consequence

TV-total boundedness on a countable discrete outcome space is equivalent to
uniform tightness on finite subsets. Here those finite subsets may include
Never, so the condition is precisely (2). TV-total boundedness implies
d-total boundedness from d≤C·TV. Conversely, a d-totally bounded family has
compact closure because the d-law space is complete. The topologies agree,
so that same closure is TV-compact and the family is TV-totally bounded.
This proves the first line of the table.

The topology statement is not a uniform reverse norm bound. For example,
uniform masses on even versus odd sites of {0,...,2L−1} have TV distance one,
but cumulative and atom differences at most 1/L, hence d=O(1/L). These two
escaping families do not form a d-Cauchy sequence. No global estimate
TV≤ω(d), with ω(ε)→0, is asserted.

## 4. Zero cumulative coefficients: atom geometry

If all a vanish, (1) reduces exactly to

    d(p,q)=max{c|ν_p−ν_q|, β‖x_p−x_q‖∞}.                (5)

When β=0 this is the interval quotient or one-point quotient in the last
two lines of the table. Assume henceforth β>0.

The finite atom vectors form

    X={x∈c₀: x_t≥0 and Σ_t x_t≤1}.

This set is closed in the supremum norm. Indeed positivity and every finite
partial-sum bound survive a uniform limit, yielding a nonnegative summable
limit of total mass at most one. Thus X is complete.

If c=0, the identification p↦x is an isometry up to β, with inverse
p(∞)=1−Σx. This proves completeness of the ACTUAL law space despite the
fact that Never mass need not be continuous in this topology. Uniform laws
on L distinct dates converge to the actual Never law as their atoms vanish.

For c>0 the same convergence is impossible: the proper uniform laws have
Never mass zero whereas Never has mass one. This produces the missing
boundary analyzed next.

## 5. The exact additional boundary when cβ>0

Use l=1−ν, the observed total finite-mass coordinate. The completion is

    X̂={ (x,l): x∈c₀, x_t≥0, Σ_t x_t≤l≤1 },             (6)

with metric

    d̂((x,l),(y,k))=max{c|l−k|, β‖x−y‖∞}.               (7)

An actual law embeds as (x,Σx). The nonnegative defect

    η=l−Σ_t x_t                                        (8)

records finite mass whose individual atoms became invisible. The separate
Never mass remains ν=1−l. In this geometry, finite diffuse mass can disappear
from every atom without becoming Never.
The defect η is determined by (x,l); it is not asserted to be a continuous
coordinate of metric (7), since the infinite sum of x is not sup-norm
continuous. Its zero set selects the actual-law image inside the completion.

Completeness: X̂ is closed in the complete product c₀×[0,1]. Positivity
and each inequality Σ_(t∈F)x_t≤l, for finite F, are closed conditions; their
intersection is (6).

Density: given (x,l), set η=l−Σx and let u_L be uniform on L finite dates.
The actual law with finite atoms x+ηu_L and Never mass 1−l has total mass
one. Its distance to (x,l) is at most βη/L. These are explicit recovery
sequences; no correlated randomness or change of observer tests is needed.

For a concrete new point, proper uniform laws on {0,...,L−1} converge to
(x=0,l=1), which has η=1 and ν=0. It is distinct from Never, represented by
(0,0). Neither a late deterministic atom nor an arbitrary relative-time
response fiber has been added: pure dates remain pairwise β-separated.
The added defect concerns diffuse finite mass, not persistent atoms.

### Actuality and properness must remain distinct

Inside the original law space, proper means ν=0. Inside X̂, a point with
ν=0 may have η>0 and fail to represent ANY actual stopping law. Actuality
requires η=0 as well. In particular, proper laws are closed in the original
metric law space when c>0, but their completion includes (x,1) with Σx<1.

This is a precise source for apparently extra boundary hypotheses: a compact
or Cauchy argument preserving zero Never mass does not by itself preserve
probability normalization in the finite atoms. The missing hypothesis is
vanishing η, not a stronger claim about the full response graph.

## 6. Total boundedness in the atom regimes

For β>0 and a_*=0, a family of actual laws is d-totally bounded if and only
if (3) holds, whether or not c is positive.

Necessity follows from a finite d-net: each center has small sufficiently
late atoms, and a uniform atom-norm approximation transfers the bound to the
family. Sufficiency follows by gridding finitely many head coordinates and,
when c>0, also gridding l in [0,1]; ignore the uniformly small late atoms.
Choosing one family member in each nonempty cell gives an internal net.

Thus mass-tightness, atom-tightness, and the separate Never coordinate have
different mathematical roles. Formula (6) shows exactly which defect remains
when atom-tightness gives compactness only in a completion.

Combining this table with the earlier proper-distance theorem gives an
intrinsic classification of proper strategic approximation. If a_*>0,
proper approximation is exactly proper TV approximation. If a_*=0 and β>0,
it is atom-tail condition (3), together with zero Never mass for every family
member when c>0. When c=0 there is no additional properness condition.
The β=0 cases follow directly from the interval/point quotient.

## 7. All-observer version and limits of the claim

No new theorem is needed for multiple observers. Their finite union simply
changes a_*,c,β. In particular, adding even one observer with a nonzero
cumulative coefficient moves the entire common-observation geometry into
the complete TV-topology case. An own-payoff diffuse boundary may therefore
disappear when effects on other players must also be controlled.

This does not identify weak convergence on the one-point compactification
with strategic convergence. It does not claim that an arbitrary payoff/cap
carrier has this finite scalar boundary. The theorem fixes one changing
clock, a finite collection of test coefficients, and uniform testing against
every deterministic marked event date. The larger continuation-state
replacement and infinity-fiber no-gos concern different objects.

## 8. Source overlap and mathematical scope

The earlier note provides the exact observable seminorm and proper-distance
formula. The present note adds its completion and general compactness
classification; it does not rederive the watchdog equilibrium argument.

Bounded source inspection found the generic discrete criterion already as
`isPMFGeneralTVTotallyBounded_iff_uniformlyFiniteTight`
(`MathUE/ProbabilityMassFunction/DiscreteTightness.lean`), the proper-TV
criterion in `MathUE/ProbabilityMassFunction/ProperStoppingApproximation.lean`,
and the distinction between late finite mass and late-or-Never mass in
`MathUE/ProbabilityMassFunction/StoppingLawFiniteTail.lean`. Specifically,
`stoppingLawLateFiniteMass` excludes Never whereas `stoppingLawLateOrNeverMass`
includes it. `IsPMFUniformlyFiniteTimeTight` uses the latter.

The existing finite operational pseudometric and compact-clock/continuation
notes were checked by narrow searches for strategic completion, diffuse
defects, atom-supremum norms, and TV topology. The sampled files do not state
classification (2)–(8). This is a bounded overlap finding, not an exhaustive
novelty claim. No literature theorem beyond elementary complete-metric,
finite-grid, and summable-mass arguments is needed here.

The completion and topological-equivalence proof passed the linked independent
review. Consolidating these cases with the seminorm note is a generic
mathematical task; no additional UE proof-search obligation is introduced.
No Lean, export, commit, or shared index was changed.
