# Computing the finite diamond test and the sharp cost of short solo periods

In the finite decision of `FINITE_SOLO_WORDS_ON_FOUR_PLAYER_DIAMONDS.md`, the exponential enumeration of binary words can be replaced by one word per reduced fraction v/p with 0<v<p≤K+1 and the two constant words. Here K is the memory length computed from the raw joining gap and contraction estimate in that theorem. The following proof also identifies the order in which the owners must occur.

Only the negative-feedback case c(0)>0>c(1) needs mixed words. The earlier theorem supplies periodicity, finite K and exact quiet tests. Write u(R)=A R+C, vmap(R)=R/(B+D R) for its two inverse-time maps, where A,B>1 and C,D>0; U uses R<θ and V uses R>θ. Strict raw joining gaps exclude equality. On any cyclic orbit the minimum follows vmap because u(R)>R, and the maximum follows u because vmap(R)<R. It therefore lies strictly inside [a,b]=[vmap(θ),u(θ)] since both maps increase. Identify the endpoints of this interval to form a circle with length b−a. The map with lift u on the left of θ and vmap+(b−a) on the right is strictly increasing except for an upward jump at the identified endpoints. Indeed the pieces agree at θ, and u(vmap(θ))>vmap(u(θ)): for any R>0,

    A R/(B+D R)+C > (A R+C)/(B+D R) > (A R+C)/(B+D(A R+C)).

Extend the lift by F(r+b−a)=F(r)+b−a. It preserves the cyclic order of any finite orbit and never identifies two of its points. The p distinct ratios around a mixed orbit of least period p therefore advance by one fixed s ranks modulo p, with 0<s<p coprime to p. The case s=0 would fix every point. This is impossible on a mixed orbit. If its sorted points are r_0<...<r_(p−1), the increasing lifts of their images are r_((j+s) mod p) with one extra circle length exactly when j+s≥p: the smallest point uses U (both labels must occur, and U occupies the left interval) and its image lies in (a,b). Thus V occurs exactly at the s wrapping ranks. In inverse time the successive labels starting from the smallest ratio are V at the jumps of floor(js/p), i.e. at step j when floor((j+1)s/p)>floor(js/p). Reverse this list to get chronological order. The symbolic period is p because the count s is coprime to p.

The K-blocks in this cyclic word have at most K+1 distinct values. In sorted-rank coordinates, the wrapped-rank set is [p−s,p) in the cyclic group of order p. After j steps its two boundaries are −(j+1)s and −js modulo p. The first K tests have only K+1 distinct boundaries and partition the ranks into at most K+1 intervals where the entire block is constant. Reversing all blocks preserves the count. On the other hand equal K-windows would force the same entire infinite past by unique determination of their predecessor in the earlier theorem. In a word of least period p their starting indices would then coincide modulo p. Therefore p≤K+1. The number of candidate fractions is at most K(K+1)/2. For rational data, K can be computed using the rational majorant log(u/l)≤u/l−1 in the earlier paper's formula. All remaining matrix and quiet comparisons are exact quadratic comparisons.

The first word realizing the strict branch choices fixes the only possible reduced fraction, even if some other quiet comparison rejects that word. For two such orbits choose their initial points in [a,b). Monotonicity and the lift identity keep their iterates within b−a of each other. Iterating through multiples of both periods gives identical numbers of wraps per step. The ordered word for that frequency is unique up to cyclic rotation, and its positive eigenray fixes its masses.

## Unbounded minimal solo periods in four-player quitting games

For every integer n≥1 there is an open set of four-player reward tables on which an exact periodic solo equilibrium gives a fixed original uniform payoff, and every periodic solo calendar with fewer than 3(n+1) cyclic distinct-owner runs per period has terminal regret bounded away from zero. The lower bound on regret depends on the table and n. Individual dates may split any run arbitrarily. Complete unilateral behavioral replacements, including Never, are allowed throughout.

## The raw family

Use strictly positive own singleton levels and the usual native subtraction. Fix positive β_U=h, β_V=1. In order X,Y,U,V take the singleton rows

    ( 0, −1,  h,      1      )
    ( 1,  0, −h,     −1      )
    (−1,  2,  0,      h/2−1  )
    (−1,  2,  1/2−h,  0      ),

where 1/2<h<2. Write J_am for the native reward when a joins m. For each positive singleton entry choose J_am positive and sufficiently near zero. At each negative entry choose J_am strictly between the entry and zero, sufficiently near that entry. All other rewards are unrestricted. The required h is given below.

We recall the elementary owner balances of the signed diamond. With every joining ratio strictly between zero and one, an exact solo calendar's complete tail consists of X_i,Y_i,B_i blocks, where B_i denotes a leaf U or V. On a change p to j its own zero continuation at the opening of j forces Γ_pj<0, and the first j comparison at the opening of p forces Γ_jp>0. The negative entry in every column prevents a final sure date or final single-color tail and positive own levels exclude Never. These arguments and the first/last substep estimates are given in the earlier diamond paper. Write b_i for the exit mass at leaf B_i=m. The intervening masses are y_i=β_m b_i and x_(i+1)=β_m b_i by X and Y indifference.

Let T=(T_U,T_V) be strictly future leaf masses after the current B_i. Row m after its leaf has unnormalized native value

    −β_m b_i + sum_l (β_l + Γ_ml) T_l = 0.

Consequently the map from T to leaf masses including the current run is M_m T with

    M_U = [[2,1/2],[0,1]],     M_V = [[1,0],[1/2,2]].

The opening native payoff of the other leaf j equals Γ_jm b_i plus the difference of the two rows' strictly future values. This difference is

    σ(T)=(1/2−h)T_U + (1−h/2)T_V

at U and its negative at V. Since J_jm>Γ_jm and J_jm<0, the first-date quiet bound forces σ(T)>0 at U and σ(T)<0 at V. In particular neither constant leaf word is possible. Both leaves recur on every periodic solution.

For R=T_U/T_V, define θ=(1−h/2)/(h−1/2). The projective backwards map for adding a leaf is

    u(R)=2R+1/2           at R<θ,
    v(R)=R/(R/2+2)        at R>θ.

Every θ>0 is attainable by h=(1+θ/2)/(θ+1/2).

## Producing the long cycle and pricing its deviations

Fix n≥1. The positive matrix M_U^n M_V has a positive Perron vector, of ratio R_0. Its Perron eigenvalue λ>1 since either matrix grows the sum of coordinates by a factor at least 3/2 on the positive cone. The formal chronological leaf word U^n V is cyclic with survival 1/λ in leaf masses. This follows by scaling the Perron vector by 1/λ and adding the leaves backwards. Each step adds one positive amount b_i to the scheduled coordinate. The only remainder left after k periods is the vector scaled by λ^(−k), so the vectors are the actual limiting tail masses. Both core masses follow from y_i=β_(B_i)b_i and x_(i+1)=β_(B_i)b_i with the same scaling.

At the V leaf the future ratio is R_0. The ratios faced by the U leaves are u^j(v(R_0)) for 0≤j<n. They strictly increase in j, since u(r)>r, and their largest value R_1=u^(n−1)(v(R_0)) satisfies R_1<R_0=u(R_1). Choose θ rational strictly between R_1 and R_0. All the prescribed leaf scores then have strict slack in their required sign.

At a leaf m the quiet leaf j has opening payoff strictly greater than Γ_jm b_i. At the preceding Y phase its value additionally includes 2β_m b_i. This is positive since 2β_m+Γ_jm>0. The incumbent leaf has corresponding values zero at its leaf and 2β_m b_i at Y. Every leaf's opening value at X is its value at Y minus x_i, strictly above its singleton contribution −x_i. For the core rows, X opens Y with zero and its singleton there is negative. At the leaf its value equals h b_i or b_i according to the leaf's column. Y opens the leaf with zero and its singleton there is negative. At X its value is x_i>0. Thus all quiet opening payoffs strictly exceed the phase mass times min(Γ_am,0). One choice of the directed J entries as described above gives strict quiet inequalities at every phase of this finite cycle. Rational values exist for all reward entries. The owner equations give zero tails at every own phase.

At each phase prescribe the hazard equal to that phase's exit mass divided by the still remaining total mass. These ratios are proper. Every player faces geometric opponent absorption every period; the owner equalities and quiet comparisons imply terminal Nash and convergence of the finite averages uniformly over all unilateral replacements. This proves the fixed original uniform target claim.

## Excluding every shorter period

Consider any periodic solo equilibrium for this table. Its positive ratios run around a periodic orbit of the two branches. Put a=v(θ), b=u(θ) and ℓ=b−a. Every cyclic orbit lies in (a,b): its maximum immediately follows a u step, as v decreases its input, and every u step has output <b. Its minimum immediately follows a v step, as u increases its input, and every v step has output >a. Extend the following definition from [a,b) to the real line by H(r+ℓ)=H(r)+ℓ:

    H(r)=u(r)  for r<θ,     H(r)=v(r)+ℓ  for r≥θ.

This real function is nondecreasing. The two formulas agree at θ. At the seam one needs u(v(θ))≥v(u(θ)). Clearing the positive denominators gives 5θ²/4+29θ/16+5/4>0. Consequently iterating H along any permitted k-periodic orbit returns its starting coordinate plus tℓ, where t counts the V steps in one period. For any two starting ratios in [a,b), the difference of their lifted iterates is at most ℓ by monotonicity and H(r+ℓ)=H(r)+ℓ. Iterating through arbitrary common multiples of two orbit lengths proves that t/k is the same on every periodic orbit. The constructed orbit has frequency 1/(n+1). Hence each periodic equilibrium has at least n+1 leaves per period and at least 3(n+1) cyclic distinct-owner runs.

For clarity, stability in the raw reward table can be seen without stability theory for circle maps. Strict signs, Perron simplicity, and strict quiet bounds persist for the exhibited word under arbitrary small perturbations of all reward cells. There are only finitely many nonconstant leaf words shorter than n+1. Each has a strictly positive matrix product and unique positive cyclic ray, depending continuously on the perturbed singleton entries. Each shorter ray violates at least one raw cap strictly: otherwise its positive masses and coarsened quiet comparisons would give an exact periodic solution, already excluded. This finite set of strict violations persists. A constant leaf tail remains excluded by the strict endpoint signs of σ (for the symmetric normalization above, σ at ratios zero/infinity). Thus exact attainment and the sharp minimum hold on an open set.

The positive terminal regret gap for all shorter periodic solo calendars follows from the exit-mass compactification and bounded-period limit in DIAMOND_SOLO_AND_JOINT_UNIFORM_EQUILIBRIUM.md. In its local-structure step, positivity of every coefficient β_l+Γ_ml suffices for identifying mixed zero corners: if the two core rows vanish, both leaf rows are strictly positive; the monotone row argument on each remaining local triple is unchanged. Each nonterminal neighborhood therefore consists of finitely many pure intervals. Its endpoint inequalities and impossibility of a final interval apply unchanged (the negative singleton and its strict joining gap occur in each column). If period survival tends to zero the limit would have only finitely many runs, and if it tends to one the limit would be diffuse with constant composition, ruled out by local pure intervals and absence of a final run. For a limiting period survival strictly between zero and one the original finitely many aggregate masses have convergent subsequences. The limit repeats the same finite word (omit zero masses and merge consecutive identical owners). The original terminal gap estimate supplies coarsened native owner and quiet comparisons for the resulting mass cycle. Its period still has at most the original number of runs, contradicting the exclusion above. Every ingredient used here persists on the open neighborhood already specified.
