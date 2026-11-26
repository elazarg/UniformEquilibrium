# A proper pair at the positive global minimum yields uniform equilibrium

At each natural date four owners independently choose Continue or Quit. The first nonempty quitting coalition determines the absorbing reward, with zero live and perpetual rewards and no public randomization. An owner can replace its complete private stopping law. For any signed original table r, center its rewards by Zᵢ(S)=rᵢ(S)−rᵢ({i}) on nonempty S only; use Zᵢ(∅)=0 in the polynomial evaluations below. Write Γᵢⱼ=Zᵢ({j}), Jᵢⱼ=Zᵢ({i,j}) and L=J−Γ, with zero diagonals. The native infimum A is over prescribed absorbing independent clocks for Z and uses the sum of the four unrestricted terminal regrets.

For a four-vector of positive odds x form the four multiaffine polynomials

    Fᵢ(x)=Σ_{∅≠T⊆I−i} (Zᵢ(T+i)−Zᵢ(T)) ∏_{j∈T} xⱼ.

Use the following finite numerical test. Choose a center a and radius r₀>0 with minᵢ aᵢ>r₀. Let D be the derivative matrix at a, assumed invertible. On the closed sup-norm cube of radius r₀ about a let H be the largest absolute value of any second partial derivative of any Fᵢ. The vertex maximum computes H since every such derivative is multiaffine. Require

    θ=9r₀ H ‖D⁻¹‖∞<1,      ‖D⁻¹F(a)‖∞<(1−θ)r₀.

The norms are the induced maximum absolute row-sum matrix norm and the maximum coordinate vector norm. Rescaling all four Fᵢ by the same nonzero number leaves this test unchanged. In every three-owner principal block T of L additionally require either a column whose two off-diagonal entries are nonpositive, or a row whose two off-diagonal entries are strictly positive.

Choose two owners i,j with Lᵢⱼ,Lⱼᵢ>0. For each owner l define Pₗ=max({0}∪{Zₗ(D):l∉D, D≠∅}). For either outsider k let Cₖ=Zₖ({i,j,k})−Zₖ({i,j}). Assume every vector v in the convex hull of the fifteen reward vectors and the zero vector, with v strictly positive and vₗ≤Pₗ for every l, meets

    vₖ ≥ Lₖᵢ xᵢ + Lₖⱼ xⱼ + Cₖ xᵢ xⱼ,     xᵢ=vⱼ/Lⱼᵢ, xⱼ=vᵢ/Lᵢⱼ

for both outsiders. This is a finite polynomial test of the original rewards; only its explicit box specialization below is used in the example.

**Theorem.** A=0. Every original table obtained by adding arbitrary signed own levels rowwise on nonempty outcomes has a uniform-equilibrium payoff. The target is fixed before accuracy; for each positive accuracy one private behavioral profile bounds every unilateral replacement and approximates the target for every sufficiently long average horizon. The existence proof is ordinary mathematics; no checked implementation of this new criterion is claimed.

Write U, B, e and N for the prescribed payoff, supremum over all finite deadlines and Never, literal Never offer, and original Never marginals. Every unilateral mixed law averages those pure offers. Let E be the zero-debt part of the compact Euclidean closure of these bounded tuples and minimize the product ν of the four original Never marginals on E. AllNever belongs to E. Suppose A>0. Its minimum α is positive: move a smallest Never marginal of actual approximants to a single finite date. This makes absorption sure. Four prescribed payoffs and three rival-dependent caps change by at most 2M times that marginal each, with M an absolute reward bound. Its owner's cap stays fixed, so A≤Σᵢ(Bᵢ−Uᵢ)+14Mν^{1/4}, also on the closure.

The cube test gives α<1. The map x↦x−D⁻¹F(x) is a contraction of that cube into itself: each Fᵢ depends on only three variables, and the derivative differs from its value at a in matrix norm by at most 9r₀H. Its fixed point has strictly positive odds and F=0. These are exactly the four product-row indifference equations against continuation zero, after dividing by positive rival-survival denominators. Play that row once followed by literal AllNever. All supported actions tie and neither a later deadline nor Never improves, since at the empty tail an owner receives its own singleton zero or perpetual zero. This is an actual native zero-debt profile with original Never strictly between zero and one.

Write v=U=B at a minimizing point. All four original Never marginals are positive, so v=e by taking limits in the full-cap defect dₗ≥Nₗ(Bₗ−eₗ). Every stage Nash row at v must be blank: a nonblank Nash prefix would preserve zero debt and strictly decrease the original product α. Finite Nash existence thus makes blank a Nash equilibrium, giving v≥0.

The possibility v=0 would allow two copies of finite approximants to this same point to be concatenated, with independent randomization. Finite approximants exist by censoring sufficiently late finite mass to Never at vanishing total variation. Insert a blank date between the copies, so the Never offer of the first finite block can be taken as a finite deadline. For the double copy with survival product ν and rival survival Hₗ on the first copy, the prescribed payoff is (1+ν)Uₗ, and the cap is max(Bₗ,eₗ+HₗBₗ). Indeed deadlines inside the first block retain their offers, the blank delimiter pays eₗ, and later deadlines compare through the second block. Both quantities tend to zero and the original joint Never tends to α²<α, impossible.

If just one coordinate is zero, a small solo hazard of its owner is already Nash. With two or three zeros T, any column j of L_T with no positive off-diagonal entry likewise gives a small solo-j root, because each other zero owner's immediate advantage is Lₖⱼqⱼ and the positive outsiders strictly wait. For two zeros with no such column both off-diagonal entries are positive; for three zeros the assumed raw test then gives a row i with both off-diagonal entries strictly positive. In either case replace every zero continuation by −ε. Nash roots of the perturbed finite game must converge to the unique blank root as ε→0, so all positive outsiders strictly wait. For that row i near blank the Quit advantage equals εHᵢ+Σ_{j∈T−i} Lᵢⱼ qⱼ+O((Σ_{j∈T−i}qⱼ)²). It is strictly positive there, even if the sum vanishes. Thus i would quit surely, contradicting convergence to blank. This proves v≫0. The prescribed and Never formulas put v in the displayed hull and under every passive bound Pₗ.

At this very v, let only i and j use the indicated positive finite odds, with hazards q=x/(1+x). Their mixing equations are vᵢ=Lᵢⱼxⱼ and vⱼ=Lⱼᵢxᵢ. An outsider's scaled wait-minus-quit advantage is vₖ−Lₖᵢxᵢ−Lₖⱼxⱼ−Cₖxᵢxⱼ, by multiplying the product-row comparison by (1+xᵢ)(1+xⱼ). This is nonnegative by hypothesis. Thus the row is Nash against the minimizer's true cap. Prepend it to actual approximants of that original point. The exact one-date full-cap recursion preserves zero debt in the limit, and the product of the original Never marginals becomes α/[(1+xᵢ)(1+xⱼ)]<α. This contradiction proves the native conclusion. For arbitrary signed row levels, if the resulting original table lacked a uniform payoff, the checked same-table normalization would give a pivot p with positive original own level sₚ for which the raw normalized game, with nonempty rewards Z/sₚ+eₚ, also lacked one. On an absorbing profile adding a nonnegative own level to a native row leaves that row's regret unchanged, since every finite reply and the prescribed profile gain it and the supremum of finite replies dominates literal Never. Thus A=0 supplies vanishing regret also on that normalized game, a contradiction to the terminal Nash criterion. [nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff](../../UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean) · [quittingSinglePivotNormalizedReward](../../UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean) · [quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors](../../UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean)

For an explicit box sufficient condition assume Pᵢ,Pⱼ>0 and put Rᵢ=Pⱼ/Lⱼᵢ, Rⱼ=Pᵢ/Lᵢⱼ. Suppose Lₖᵢ,Lₖⱼ≤0 and Cₖ≤−Lₖᵢ/Rⱼ−Lₖⱼ/Rᵢ for each outsider. Then the two displayed quiet inequalities hold throughout the box: dividing their right sides by xᵢxⱼ gives Cₖ+Lₖᵢ/xⱼ+Lₖⱼ/xᵢ≤0. A strictly positive Cₖ is permitted and blocks the sure pair with both outsiders waiting.

## A four-player class

Take
```
Γ = [  0 -1  4 -1; -1  0 -1  4;  4 -1  0 -5; -1  4 -5  0 ]
20(Γ−J) = [ 0 -13 49 -40; -4 0 -32 37; 69 30 0 -57; 22 73 -34 0 ] .
```
For the concrete completion below, the two anchor owners have passive maxima 4 and both outsiders have Cₖ=1/20. With anchor 01 the two positive L entries are 13/20 and 1/5, so R₀=20,R₁=80/13. For owner 2 the negative L magnitudes on columns 0,1 are 69/20 and 3/2. For owner 3 they are 11/10 and 73/20. Both outsider thresholds strictly exceed 1/10. On triples 012 and 013 the required strictly positive L row is 1 and 0 respectively. On triples 023 and 123 the strictly negative L column is 0 and 1 respectively. All these signs survive small independent perturbations. A pure sure anchor 01 with the outsiders waiting is blocked by either strictly positive Cₖ.

## A completion outside stationary, sure-first and two-pair calendars

Here is an explicit completion. Rows in the display are the four native rewards multiplied by 20. The coalition mask is the sum of 2ⁱ over its members, and the lines are in mask order 1 through 15. Take every original signed level equal to 10 for the nonexistence comparisons; the uniform-payoff conclusion applies separately to every choice of levels.

```
0 -20 80 -20;  -20 0 -20 80;  -7 -16 140 -180;
80 -20 0 -100;  31 60 11 -80;  0 12 -50 60;  -100 -160 141 -140;
-20 80 -100 0;  20 20 0 -42;  -60 43 -160 7;  0 140 -160 -179;
-20 60 -43 -66;  -140 -40 -160 40;  60 140 -180 0;  20 0 100 -60.
```

For the cube test use 20F in place of F. In owner order 0,1,2,3 its polynomials are

    13x₁−49x₂+40x₃−100x₁x₂+60x₁x₃−120x₂x₃−40x₁x₂x₃,
    4x₀+32x₂−37x₃−220x₀x₂+120x₀x₃+80x₂x₃+40x₀x₂x₃,
    −69x₀−30x₁+57x₃+x₀x₁−160x₀x₃−20x₁x₃+260x₀x₁x₃,
    −22x₀−73x₁+34x₂+x₀x₁+120x₀x₂−60x₁x₂+80x₀x₁x₂.

Take a=(17854782,8451799,19554700,48393925)/10⁸ and r₀=10⁻⁵. Direct rational evaluation gives ‖D⁻¹‖∞<115/1000 and ‖D⁻¹(20F)(a)‖∞<21/10¹⁰, with D the derivative of 20F. Every cube coordinate is between 0 and 1, so H≤480 from the quadratic and cubic coefficients. Thus θ<1/200 and the remaining contraction inequality holds strictly. This proves uniform equilibrium throughout a full open neighborhood of the sixty actual rewards, with arbitrary signed own levels. No supposition about a supplied continuation, strategy or unknown minimizing payoff is required.

The passive maxima for owners 0,1 are both 4 and the two quiet increments at 01 are both 1/20. There is no stationary exact terminal Nash profile, no sure first-date product equilibrium supported by any behavioral continuation, and no periodic exact terminal Nash profile that alternates two fixed disjoint pairs, even when some scheduled hazards are zero. We give reproducible finite arithmetic certificates below. There is no assertion here that every other possible finite word, including arbitrarily long ones, fails.

For the stationary test write q in the closed four-cube. Against player i, let Hᵢ be rival all-continue probability, Qᵢ its forced Quit offer, and Pᵢ the passive immediate absorption contribution. With at least two active players, every one faces eventual rival absorption; the sign of its stationary advantage is the sign of Fᵢ=(1−Hᵢ)Qᵢ−Pᵢ. Thus qᵢ>0 implies Fᵢ≥0 and qᵢ<1 implies Fᵢ≤0. If only i is active, its negative mate k in 01 or 23 has Γₖᵢ<0 and Jₖᵢ>Γₖᵢ. That outsider's stationary prescribed payoff is sₖ+Γₖᵢ while immediately quitting yields sₖ+qᵢJₖᵢ>sₖ+Γₖᵢ. AllNever is excluded by the positive own levels.

For a sure first date, a subsequent behavioral cap is at least sᵢ+bᵢ, where bᵢ is the greater of the minimum native participant reward and the minimum of zero and all native passive rewards. The first bound follows by immediate Quit. For the second take arbitrarily late finite deadlines against any particular opponent continuation. The tie probability tends to zero and waiting through all rival finite deadlines or exiting alone always gives at least the stated native minimum in the limit; the original finite response gains sᵢ. At this table b=(−3,−2,−8,−179/20). At least one hazard is sure, so Hᵢ=0 unless i alone is sure. Thus Fᵢ=Qᵢ−Pᵢ−bᵢHᵢ must satisfy the same two cube sign conditions, also for the unique sure player where only Fᵢ≥0 is needed. This checks all possible post-date prescriptions at once.

For each tested partition let m denote i's scheduled mate, T the two owners scheduled at the other phase, τ=∏_{j∈T}(1−qⱼ), and Hᵢ=(1−qₘ)τ. Write Pᵢᵀ for the expected native reward to i from a nonempty T quit set (zero at the empty set), and Qᵢᵀ for the expected forced Quit reward against T alone. A sure reachable date was excluded above, including at the second phase by conditioning on survival. With at least two positive scheduled hazards every player faces eventual rival absorption. Waiting forever stays in every player's supported actions at both phases, so all finite deadlines are bounded by the Never value, and every scheduled positive hazard ties it. Summing the geometric passive returns at the two phases gives the necessary conditions

    Aᵢ=(1−Hᵢ)Jᵢₘqₘ−qₘΓᵢₘ−(1−qₘ)Pᵢᵀ ≤0,     qᵢAᵢ=0,
    Dᵢ=(1−Hᵢ)Qᵢᵀ−Pᵢᵀ−τqₘΓᵢₘ ≤0 .

If just one owner is active, its negative mate can instead Quit at an empty phase before future absorption or at the active phase with expected native offer qᵢJₖᵢ>Γₖᵢ, so no such schedule works.

Here are the complete subdivision instructions for all eight collections of boxes. They use only the displayed payoff table. Set Zᵢ(∅)=0 in polynomial evaluations. The stationary and two-phase fields have coordinatewise degree at most two; the sure fields have degree one. One can obtain each initial field's tensor Bernstein coefficients by multiplying out its polynomial in the hazard coordinates q. A monomial ∏qₖ^{aₖ} contributes its coefficient times ∏[binom(bₖ,aₖ)/binom(n,aₖ)] to tensor entry b of common degree n, interpreted as zero if any bₖ<aₖ. For the sure test restrict to the face with the named coordinate fixed at one. The sign rules below are applied to a closed box with lower and upper corners l,h. A binary split is at the midpoint, cycling through the free coordinate indices in ascending order, starting at coordinate 0 or the least free coordinate. In degree two each line (L,C,R) in the split dimension gives the two new lines (4L,2(L+C),L+2C+R) and (L+2C+R,2(C+R),4R); in degree one (L,R) gives (2L,L+R) and (L+R,2R). These are usual Bernstein midpoint subdivision with a positive scalar common to all coefficients of that box, preserving every sign.

For the stationary and sure faces, reject if some i has lᵢ>0 with maximum Bernstein coefficient of Fᵢ strictly negative, or hᵢ<1 with minimum coefficient strictly positive. For the two-phase fields reject if any of the eight fields has strictly positive minimum coefficient, or if lᵢ>0 and Aᵢ has strictly negative maximum coefficient. At the stationary and two-phase tests, before a sign check close as an origin box whenever max hᵢ≤1/512. Indeed M=9 bounds the native payoffs. Setting s=max qᵢ, for the respective active equation the residual Fᵢ or Aᵢ equals −(Γq)ᵢ to within 18Ms². The immediate Quit contribution is bounded by 9Ms² since its conditional offer magnitude is ≤3Ms and 1−Hᵢ≤3s. In the corresponding one-cycle passive return the singleton probabilities differ from qⱼ by at most 2s² each and the total probability of multiple finite rivals is ≤3s², for an additional ≤9Ms². These estimates apply also to the two-phase passive ordering. For every principal block Γ_SS of size at least two the maximum absolute inverse row sum is ≤3, checked on the six pairs, four triples and full matrix. All active coordinates on this small cube are strictly below one, and their equations have zero residual, forcing s≤54Ms². Since 54M=486<512, an origin box contains no nonzero solution on such a support. Single-owner and all-blank possibilities were dealt with directly.

The resulting complete binary-tree counts, including root and rejected leaves, are

| test | nodes | origin boxes | maximum depth |
|---|---:|---:|---:|
| stationary | 11747 | 1 | 52 |
| sure owner 0 | 677 | 0 | 20 |
| sure owner 1 | 269 | 0 | 15 |
| sure owner 2 | 41 | 0 | 8 |
| sure owner 3 | 45 | 0 | 9 |
| phases 01 and 23 | 6511 | 1 | 52 |
| phases 02 and 13 | 7787 | 1 | 52 |
| phases 03 and 12 | 7573 | 1 | 52 |

For every listed tree no boxes remain after the two indicated leaf rules. The finite sign certificates are strict on their tested faces, including strict elimination of the single active cases. The analytic origin bound also has slack. Thus the failure of these specific calendar mechanisms persists for sufficiently small full reward perturbations. The cube, triple and positive-source conditions have strict slack at this center, with the passive maxima continuous in the reward entries, so the uniform-payoff region and these mechanism exclusions have a common open neighborhood.

There are also short direct checks against previous payoff, support and ledger criteria. The two positive participant pairs 02 and 13 cover all four players. Every nonempty marked set therefore intersects a coalition all of whose participants receive strictly positive native rewards, ruling out ordered nonpositive anchor blocks and the product-low criterion. At coalition 01 the two outside joining increments C₂ and C₃ are both 1/20. A nonnegative support-filtered ledger w with weighted joining sum nonpositive on every nonempty proper coalition must have w₂=w₃=0. Its required nonnegative welfare on singleton 0 and singleton 1 then forces w₁=w₀=0. Thus no nonzero ledger exists, regardless of how its support is chosen.

On the 012 support take odds t(1,1/10,2) in owner order. At small t all three Quit premiums are positive: the three coefficients to first order are 613/200, 2/5, 3/10. The derivative of the three polynomial indifference levels at zero is L_012, of determinant −2853/1000. Its negative sign persists and violates the required three-owner orientation on the positive-Quit region. This also rules out the localized orientation tests: the reward hull contains an open ball about zero, since the five mask vectors 1,2,4,5,10 are affinely independent and have positive zero-barycenter weights (8068,8076,3723,1680,3140)/24687. The first-action outer set contains zero (take the blank row), so every allowed open thickening of it also contains an open ball about zero. In either domain take the three indicated indifference levels O(t) and a strictly negative fourth coordinate −t. Thus the violating orientation is genuinely present in each permitted projected domain. The boxed-charge alternative on support 012 also fails already at singleton 2: the sum J₀₂+J₁₂=43/20 is positive. These checks do not purport to exhaust arbitrary nonstationary constructions.

## An explicit equilibrium on the displayed table

There is also a proper period-two equilibrium on this example. Starting at phase 0, alternate the deterministic sets B₀={0} and B₁={1,2,3}. Whenever its phase recurs, owner i independently quits with the same conditional probability qᵢ, and at the other phase continues surely. There is no random choice of date or phase shared by the players.

Here are finite rational tests producing the four probabilities. For i,t average over independent subsets S of Bₜ∖{i}, with inclusion probabilities qⱼ. Write Hᵢₜ=Pr(S=∅), Pᵢₜ=E[Zᵢ(S)] using Zᵢ(∅)=0, and Qᵢₜ=E[Zᵢ(S∪{i})]. Put hᵢ=Hᵢ₀Hᵢ₁ and

    Vᵢₜ=(Pᵢₜ+HᵢₜPᵢ,₁₋ₜ)/(1−hᵢ),
    Dᵢₜ=20[(1−hᵢ)Qᵢₜ−Pᵢₜ−HᵢₜPᵢ,₁₋ₜ].

Let Fᵢ be Dᵢₜ at i's scheduled phase, Eᵢ the field at the other phase. Set a=(45680793,22187802,24501004,34745724)/10⁸ and ρ=10⁻⁶. Direct rational evaluation gives ‖DF(a)⁻¹‖∞<83/1000 and ‖DF(a)⁻¹F(a)‖∞<41/10¹⁰. For a polynomial g let c(g) be the sum of the absolute monomial coefficients. Expanding the displayed fields gives maxᵢⱼₖ c(∂ⱼ∂ₖFᵢ)=1457 and maxᵢ Σⱼc(∂ⱼEᵢ)=20404. The four Eᵢ(a) are respectively less than −3.24, −8.65, −9.94 and −2.62. Thus q↦q−DF(a)⁻¹F(q) maps the closed radius-ρ sup-norm cube into itself, with contraction constant at most 16·1457·(83/1000)ρ<1/500. At its unique fixed point all hazards lie strictly between zero and one and all four off-phase fields are negative, since 20404ρ<0.021.

Against the other three owners, literal Never has value Vᵢₜ starting at phase t, by its geometric series with cycle survival hᵢ<1. At any reached date, a finite deadline's Quit payoff Qᵢₜ equals this value when scheduled and is strictly smaller at every unscheduled date. The Never values satisfy Vᵢₜ=Pᵢₜ+HᵢₜVᵢ,₁₋ₜ. Iterating this recursion bounds every deadline and gives equality for the prescribed mixtures, with vanishing terminal remainder at rate hᵢ per cycle. Any unilateral behavioral replacement averages these comparisons. Opponents alone therefore ensure geometric absorption under every deviation. Adding any signed row levels s preserves all comparisons, and the expected average payoff tends to the terminal payoff uniformly over deviations, since the expected number of pre-absorption dates is uniformly bounded. The phase-0 target is exactly s+(Vᵢ₀)ᵢ, with V₀₀=0. These strict root and quiet tests persist nearby; they are a second proof at the example. The general positive-minimum theorem above uses the one-date seed and the minimizing continuation.

The earlier triple–singleton collision-box theorem requires all six ordered internal joining gaps Lᵢⱼ to be positive. Every triple contains 02 or 13, with both internal directions negative, so no choice of roles meets its test. The signed solo/triple quadratic theorem uses a different schedule with r recurring within the triple and o always quiet. For completeness its 24 role choices (r,j,k,o) all have invertible first linear system; only three, up to swapping j,k, return positive reciprocal odds. Its respective second-stage quadratics, up to nonzero constants, are

| (r,j,k,o) | polynomial at b |
|---|---|
| (0,1,2,3) | 118782209 b²−218602894 b+32444720 |
| (0,2,3,1) | 85073044838 b²−115521318269 b+152262446231 |
| (1,0,3,2) | 39895465337 b²−148112987814 b−28968207320 |

Only the first has a root in (0,1), with 0.1628<b<0.1629. At that root the implied solo hazard is [(−10640/12493)b²+(780233b+6072)/812045]/[(1−b)(10640b/12493−161920/162409)]<0. Thus neither raw producer supplies this example. A periodic-certificate theorem already verifies supplied hazards and continuation values. The construction above determines them from this reward table. [isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate](../../UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean)
