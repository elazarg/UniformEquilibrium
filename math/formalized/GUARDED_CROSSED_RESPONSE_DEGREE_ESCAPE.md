# Guarded crossed-response degree escape for quitting games

## 1. Exact statements and strategic scope

Let I be a finite player set of cardinality n ≥ 3. A quitting game specifies
a real vector r(S) ∈ Rᴵ for each nonempty coalition S ⊆ I. At dates
t = 0,1,..., each player chooses Continue or Quit. The first nonempty
simultaneous quitting coalition absorbs. Its reward is paid at every stage
after the quitting date; live rewards and infinite all-Continue (Never) pay
zero. Rewards may have arbitrary signs.

Randomization is private and independent across players. Before absorption
the only history is all-Continue, so a complete behavioral strategy is
equivalently a private law on N ∪ {Never}. Conditional hazards implement any
such law, and independent first-Quit times implement any behavioral profile.
A unilateral replacement may use any law on this entire set, including
Never. No public correlation or joint deviation is introduced.

Write Uᵢ(σ) for terminal payoff, Bᵢ(σ)=sup_τ Uᵢ(τ,σ₋ᵢ) for the complete
behavioral response cap, and E(σ)=maxᵢ(Bᵢ(σ)−Uᵢ(σ)). Let gᴴ be H-stage
average payoff: absorption at date t carries weight max(H−t−1,0)/H.
A uniform-equilibrium payoff is one fixed v such that, for every ε>0,
there exist one profile σ and one H₀ with, for every H≥H₀,

    ‖gᴴ(σ)−v‖∞ < ε,
    gᴴᵢ(τ,σ₋ᵢ)−gᴴᵢ(σ) ≤ ε   for every i and every complete replacement τ.

The profile and threshold may depend on ε; v may not.

Put sᵢ=rᵢ({i}) and Γᵢⱼ=rᵢ({j})−sᵢ. Rows are payoff recipients and columns
are singleton quitters, so Γ has zero diagonal. Matrix inequalities below
are entrywise. For a square real matrix A define

    f_A,c(x)=min(x,Ax+c),

coordinatewise on all of Rᴵ. A is R0 if f_A,0 has only the zero root.
For R0 A, κ(A) is the integer degree of f_A,0 about that root.

Choose distinct players a,b, put J=I∖{a,b}, and choose h∈(0,1]. Let P
exchange coordinates a,b and fix every other coordinate. Define stationary
residual polynomials Δ in Section 2.

### Theorem A: guarded common-height degree escape

Suppose Γₐᵦ>0 and Γᵦₐ>0. For each selected i and its partner j suppose

    Δᵢ(qⱼ=0,z)>0   for every nonzero z∈[0,1]ᴶ,
    Δᵢ(qⱼ=h,z)<0   for every z∈[0,1]ᴶ.                 (Gₕ)

If A=PΓ is R0 and κ(A)≠1, the original game has an exact stationary
terminal equilibrium against every behavioral replacement, at hazards q with

    0<qₐ<h,       0<qᵦ<h,       qᴶ≠0.                 (A1)

Every opponent-deleted clock contracts. The same stationary profile delivers
its actual terminal payoff uniformly over all sufficiently long horizons.
The entire nonzero fixed-point set of the constructed crossed map has total
degree 1−κ(A). This is neither a count of roots nor their index under the
ordinary unswapped Nash map.

The ceiling is imposed only on an auxiliary map. Actual players retain both
actions, every hazard, every deadline, and every behavioral replacement.

### Theorem B: finite strict raw-table classes

For i=a,b, with partner j, define the lower ranking test

    min_(T⊆J) rᵢ(T∪{i}) > max_(∅≠T⊆J) rᵢ(T).        (L)

If det Γ>0, Γ⁻¹>0, and (L) holds, either of the following upper tests gives
the exact stationary and uniform conclusion of Theorem A:

1. For any finite n≥3, the unit-ceiling joining test

       rᵢ(T∪{i,j}) < rᵢ(T∪{j})   for every T⊆J,       (U)

   with h=1.
2. For n=4, label the pair 0,1 and outsiders 2,3. Expand
   fᵢ(x,y)=Δᵢ(qⱼ=1/2,q₂=x,q₃=y) in the degree-(2,2) tensor Bernstein
   basis, as defined in Section 3. Every one of its nine coefficients is
   strictly negative, for each selected i. This gives h=1/2.

The full matrix Γ is R0 with κ(Γ)=+1 in both strict classes. The crossed
matrix has κ(PΓ)=−1, so the nonzero modified fixed-point set has total
degree +2. No regularity of these fixed points is required.

### Theorem C: weak inverse and weak half-ceiling boundary

The following raw conditions produce one fixed uniform-equilibrium payoff,
with stationary profiles of complete terminal regret tending to zero:

- For any n≥3: det Γ>0, Γ⁻¹≥0, and the strict tests (L),(U).
- For n=4: det Γ>0, Γ⁻¹≥0, all comparisons in (L) weak, and all eighteen
  half-ceiling Bernstein coefficients nonpositive.

There is no supplied punishment plan, no supplied root, and no restriction
on singleton signs. Exact stationary attainment at the weak boundary is
not asserted. A payoff subsequence fixes the target before final accuracy
and horizon are chosen.

### Theorem D: sixteen weak comparisons, no matrix assumption

For four players choose an ordered pair (a,b) and J=I∖{a,b}. Suppose only

    min_(T⊆J) rₐ(T∪{a}) ≥ max_(∅≠T⊆J) rₐ(T),
    rᵦ(T∪{a,b}) ≤ rᵦ(T∪{a})   for every T⊆J.          (D1)

These are twelve weak lower comparisons for a and four weak joining
comparisons for b. The original signed game has a uniform-equilibrium
payoff, with no matrix hypothesis and no approximation of the raw guards.
More generally it suffices that

    Δₐ(qᵦ=0,z)≥0 for nonzero z∈[0,1]ᴶ,
    Δᵦ(qₐ=1,z)≤0 for every z∈[0,1]ᴶ.                 (D2)

The direct construction has a sure and b Never. If its outsider hazards
are nonzero, it is exact stationary behavioral Nash. If all are zero, a
negative singleton may require an off-path punishment argument using the
four-player source theorem in Section 6.4. The unconditional conclusion is
existence of a fixed UE payoff, not exact stationary attainment or the
interior, at-least-three-active conclusion of Theorem A. In particular the
full-ceiling UE assertion alone does not require degree theory in Fin4.

### Conjecture-facing content

These are explicit reward-table existence classes, not characterizations of
tables already admitting a favorable strategy. The guards produce usable
original-game roots after a row permutation of the auxiliary residual map.
This requires no response-row equality and no identification of hazards.
The examples below have full singleton degree +1 and no nondiscrete
response-invariant partition, so the new criterion covers tables not covered
by a degree-escape test on the full matrix or a response-invariant quotient.
The half-ceiling example additionally fails every proper-child raw domination
test defined in Section 8. The class contains a full sixty-dimensional
reward neighborhood.

These statements are ordinary mathematics. They neither assert that every
Q matrix yields UE nor cover arbitrary nonsingleton completions of a fixed
matrix. Failure of the guards supplies no alternative equilibrium producer.
Theorem D is a simpler additional producer with a wider full-ceiling raw
class, whereas Theorems A and B prove the stronger interior stationary output.

## 2. Stationary algebra and the original incentives

For q∈[0,1]ᴵ put

    αᵢ(q)=∏_(j≠i)(1−qⱼ),
    πᵢ(T;q)=∏_(j∈T)qⱼ ∏_(j∉T,j≠i)(1−qⱼ),
    Qᵢ(q)=Σ_(T⊆I∖{i}) πᵢ(T;q) rᵢ(T∪{i}),
    Hᵢ(q)=Σ_(∅≠T⊆I∖{i}) πᵢ(T;q) rᵢ(T),
    Δᵢ(q)=(1−αᵢ(q))Qᵢ(q)−Hᵢ(q).                    (2.1)

No empty-coalition reward is introduced. Hᵢ is the one-stage Continue
absorption contribution, not its stationary continuation payoff. These
formulas extend polynomially to all of Rᴵ, and Δᵢ is independent of qᵢ.
Since Qᵢ=sᵢ+O(‖q‖), 1−αᵢ=Σⱼ≠ᵢqⱼ+O(‖q‖²), and
Hᵢ=Σⱼ≠ᵢqⱼrᵢ({j})+O(‖q‖²),

    Δ(q)=−Γq+O(‖q‖²)                                (2.2)

on a whole ambient neighborhood of zero.

For q≠0 in the cube, let C(q)=∏ᵢ(1−qᵢ), η(q)=1−C(q), and
Rᵢ(q)=qᵢQᵢ(q)+(1−qᵢ)Hᵢ(q). Then η>0, and repeating the product root has
actual terminal payoff

    vᵢ(q)=Rᵢ(q)/η(q).                                (2.3)

Indeed v=R+Cv, with a geometrically vanishing surviving remainder. Using
C=(1−qᵢ)αᵢ gives the exact identity

    η[Qᵢ−Hᵢ−αᵢvᵢ]=Δᵢ.                              (2.4)

Thus the original individual stationary endpoint conditions are

    qᵢ=0 ⇒ Δᵢ≤0;  0<qᵢ<1 ⇒ Δᵢ=0;  qᵢ=1 ⇒ Δᵢ≥0.     (2.5)

They imply Qᵢ≤vᵢ and Hᵢ+αᵢvᵢ≤vᵢ. These are not by themselves complete
behavioral Nash conditions for a negative sole quitter: that owner could
choose Never. Theorem A will ensure αᵢ<1 for every player, which prices
every such replacement without a separate punishment argument.

## 3. Finite raw tests for the guards

With the partner absent, let β=∏_(k∈J)(1−qₖ),
ℓ=min_(T⊆J)rᵢ(T∪{i}), and b=max_(∅≠T⊆J)rᵢ(T). Then
Qᵢ≥ℓ, Hᵢ≤(1−β)b, and

    Δᵢ≥(1−β)(ℓ−b)>0                                  (3.1)

whenever an outsider hazard is positive. Thus (L) gives the lower guard.
At a sure partner αᵢ=0, and Δᵢ is an average of the joining differences
in (U); all are strictly negative, so (U) gives the upper guard at h=1.
For four players these are twelve lower comparisons and four upper
comparisons per recipient, thirty-two strict linear inequalities in total.

For h=1/2 and four players, fᵢ(x,y) has degree at most two separately in x
and y. Its unique tensor Bernstein expansion is

    fᵢ(x,y)=Σ_(u,v=0)² cᵢᵤᵥ Bᵤ(x)Bᵥ(y),
    B₀(x)=(1−x)², B₁(x)=2x(1−x), B₂(x)=x².            (3.2)

Compute coefficients by evaluating on {0,1/2,1}² and applying in each
variable the interpolation rule

    c₀=f(0), c₂=f(1), c₁=2f(1/2)−(f(0)+f(1))/2.       (3.3)

Each coefficient is a rational linear combination of the fifteen rewards
in that recipient's row. The basis functions are nonnegative and sum to
one. Strict negative coefficients give the upper guard everywhere; weak
coefficients give its weak version. This sufficient test is not equivalent
to polynomial negativity on the square. Together with (L), it uses
twenty-four lower comparisons and eighteen upper coefficient inequalities.

Reciprocal positivity is derived in Theorems B and C. The weak lower test
implies Γᵢₖ≤0 for each outsider k. If Γᵢⱼ≤0 too, the whole selected row
would be nonpositive. Its product with the nonnegative i-th column of Γ⁻¹
could not equal one. Therefore Γₐᵦ,Γᵦₐ>0.

The polynomial guards (Gₕ), rather than these particular linear tests, may
also be checked directly. They quantify over a finite bounded real cube in
explicit reward polynomials, not over strategies or equilibria.

## 4. Crossed fixed points and ambient integer degree

Let Rₕ be the box with selected coordinates in [0,h] and all other
coordinates in [0,1], and define on all of Rᴵ

    T(q)=clip_Rₕ(q+PΔ(q)),       Z(q)=q−T(q).           (4.1)

This interchanges two residual coordinates without interchanging utilities
or granting joint agency. Any fixed point lies in Rₕ.

Suppose q is fixed and qᴶ≠0. If qₐ=0, the lower guard for recipient b
makes Tₐ(q)>0, a contradiction. If qₐ=h, the upper guard for b makes
Tₐ(q)<h. Thus 0<qₐ<h, and likewise 0<qᵦ<h. Their two equations force
Δₐ=Δᵦ=0. The other coordinates use their own residuals, so all original
conditions (2.5) hold, including outsider zero and sure faces.

There is no nonzero fixed point with qᴶ=0. For selected i with partner j
of hazard t,

    Δᵢ(t,0)=t[(1−t)(sᵢ−rᵢ({j}))
                    +t(rᵢ({i,j})−rᵢ({j}))].           (4.2)

The bracket is affine in t. At zero it is −Γᵢⱼ<0; at h it is negative
by the upper guard. It is therefore negative for every t∈[0,h]. A positive
crossed j-coordinate cannot be fixed when Δᵢ<0. Both selected hazards must
vanish, leaving only the origin. Every nonzero fixed point consequently
satisfies (A1) and all original individual incentives.

Set Ω=(−1,2)ᴵ. The image of T lies in Rₕ strictly inside Ω. Homotope T
to the center of Rₕ; throughout, its image stays inside Rₕ, so there is no
boundary fixed point. Normalization of Brouwer degree gives

    deg(Z,Ω,0)=+1.                                    (4.3)

All roots on the strategy-cube boundary are retained in this ambient domain.
Near zero upper clipping is inactive, though lower clipping is not. Hence

    Z(q)=min(q,−PΔ(q))=min(q,Aq+O(‖q‖²)),  A=PΓ.       (4.4)

R0 means min(x,Ax) has no nonzero zero even in the whole real space: its
zeros are exactly x≥0, Ax≥0, xᵢ(Ax)ᵢ=0. By compactness and positive
homogeneity there is c_A>0 with

    ‖min(x,Ax)‖∞≥c_A‖x‖∞.                             (4.5)

Coordinatewise minimum is 1-Lipschitz in its second argument. Thus the
quadratic perturbation in (4.4) is smaller than this margin on a sufficiently
small sphere, and its straight homotopy is boundary-zero free. Zero is
isolated and has local degree κ(A). Excision and additivity give degree
1−κ(A) on Ω with a small closed neighborhood of zero removed. If κ(A)≠1,
this open annulus has a zero. The preceding fixed-point argument makes it
an original-game equilibrium root. No differentiability of the clipped map
at zero or regularity of a nonzero root is assumed.

These uses of normalization, homotopy, excision, additivity, and nonzero-
degree existence are the usual properties of Brouwer degree. The ambient
minimum convention and the LCP index convention are as in Gowda [1].

### Strict inverse positivity computes the index

If det Γ>0 and Γ⁻¹>0, then A⁻¹=Γ⁻¹P>0 and det A<0. For a homogeneous
complementary pair x≥0,w=Ax≥0 with x≠0, invertibility gives w≠0. Thus
x=A⁻¹w>0, and complementarity forces w=0, a contradiction. So A is R0.

Every solution of LCP(A,−1) has x=A⁻¹(1+w)>0, so w=0 and x=A⁻¹1 is
its unique solution. Near it, min(x,Ax−1) selects Ax−1, and its local
degree is sign(det A)=−1. For R0 A, solutions for bounded right-hand sides
are uniformly bounded: otherwise normalize an unbounded sequence of
solutions to obtain a nonzero homogeneous complementary solution. Homotopy
in the right-hand side then proves κ(A)=−1. Applied to Γ, the same argument
gives full R0 and κ(Γ)=+1. This proves Theorem B from Theorem A.

### A useful matrix restriction with explicit premises

Suppose Γ itself is R0, Γₐᵦ,Γᵦₐ>0, and Γₐₖ,Γᵦₖ<0 for every k∈J.
Then PΓ is R0. Indeed, let x=(u,z)≥0 and w=PΓx≥0 be complementary.
If z=0, wₐ=Γᵦₐuₐ and wᵦ=Γₐᵦuᵦ force u=0. If z≠0, the strict external
signs force uₐ,uᵦ>0; hence wₐ=wᵦ=0. Swapping these zero slacks changes
nothing, so Γx=w and x is a homogeneous complementary Γ solution, again
zero. Thus in this explicitly specified matrix region any no-UE game
passing (Gₕ) must have κ(PΓ)=1. This does not infer R0 or degree from the
standard-Q property alone.

## 5. Complete behavioral equilibrium and literal implementations

For the produced root at least three hazards are positive, so αᵢ<1 for
every i. Against fixed stationary opponents, quitting at date t has payoff

    Hᵢ(1−αᵢᵗ)/(1−αᵢ)+αᵢᵗQᵢ,

and Never has payoff Hᵢ/(1−αᵢ). Any complete response is a mixture of these
deadline values. Hence its exact cap is

    Bᵢ=max(Qᵢ,Hᵢ/(1−αᵢ))≤vᵢ.                        (5.1)

The inequalities follow from (2.5) and the Bellman recursion. Prescribed
play attains vᵢ, so Bᵢ=Uᵢ=vᵢ. This proves exact terminal Nash even for
negative sᵢ: opponents absorb almost surely after deleting any player.

Let M>0 bound every absolute terminal reward. The first opponent quit Lᵢ
is geometric, with E[Lᵢ+1]=1/(1−αᵢ). Under any complete i-replacement,
absorption occurs no later than Lᵢ. Therefore

    |gᴴᵢ(τ,q₋ᵢ)−Uᵢ(τ,q₋ᵢ)|≤M/[H(1−αᵢ)].           (5.2)

This bound is uniform over all response laws. Prescribed payoffs converge
to v, and horizon-H regret is at most maxᵢ 2M/[H(1−αᵢ)]. The same q and
the same target v work for all accuracies after increasing H. Theorem A's
full behavioral and uniform claims follow.

For a finite independent-law implementation, retain N≥1 stationary dates
and move each player's entire later private mass to Never. Call the profile
pᴺ, and write ρ=maxᵢαᵢ<1. Exact renewal gives

    Uᵢ(pᴺ)=(1−Cᴺ)vᵢ.                                  (5.3)

Couple stationary and censored opponents against the same arbitrary complete
i-response. Outcomes can differ only if every opponent survives N dates,
an event of probability αᵢᴺ. Thus

    Bᵢ(pᴺ)≤vᵢ+2Mαᵢᴺ,
    E(pᴺ)≤3Mρᴺ,       ‖U(pᴺ)−v‖∞≤Mρᴺ.                (5.4)

These bounds do not restrict deviations to the retained menu. The number
of dates is logarithmic in inverse accuracy for each fixed root when ρ>0;
if ρ=0 one date suffices.

For completeness, the finite laws also satisfy

    horizon-H regret ≤ 3Mρᴺ+2M(N+1)/H,
    delivery error  ≤ Mρᴺ+M(N+1)/H.                    (5.5)

To verify the signed cap comparison, consider a pure response. An early
response absorbs before N or Never, giving the usual M(N+1)/H comparison.
For a response after the opponents' support, if sᵢ≥0, discounting its solo
contribution by the horizon weight cannot increase it above its terminal
value. If sᵢ<0, compare instead with Never: the late solo contribution is
nonpositive, while all earlier opponent outcomes are unchanged. This bounds
the finite-horizon payoff by the complete terminal cap plus M(N+1)/H.
Mixtures inherit the inequality. Prescribed finite laws have only early
absorption or Never, so their payoff comparison is two-sided, proving (5.5).
No two-sided uniform limit for every late response is claimed.

For rational rewards and rational h, the root conditions in Theorem A are
a nonempty finite semialgebraic system over Q and admit a real-algebraic
solution. Alternatively, rational hazards can be enumerated and their full
caps evaluated by (5.1). In a neighborhood of the produced root every
denominator 1−αᵢ stays positive, so payoff and cap are continuous there.
Rational density ensures that this accuracy-only search eventually finds
any requested positive regret tolerance. Censoring then adds the error in
(5.4), together with the initial small regret. This is neither a practical
complexity estimate nor an oracle for a previously specified real target.

## 6. Weak boundaries and the matrix-free full-ceiling theorem

### 6.1 Strictifying a nonnegative inverse

For n≥3 let B=Γ⁻¹≥0 and K be the matrix with zero diagonal and every
off-diagonal entry one. For sufficiently small e>0,

    Γ_e=Γ−eK,
    Γ_e⁻¹=B+eBKB+e²BKBKB+⋯>0.                         (6.1)

The series converges when e‖BK‖<1 and every term is nonnegative. To prove
strict positivity, fix (i,j). If Bᵢⱼ or (BKB)ᵢⱼ is positive, there is
nothing to show. Otherwise

    (BKB)ᵢⱼ=Σ_(u≠v)BᵢᵤBᵥⱼ=0

forces the nonempty supports of row i and column j of B to be the same
singleton {k}. There is Bᵤᵥ>0 with u,v≠k: otherwise the n−1≥2 rows
outside k are all supported only in column k, contradicting invertibility.
Then BᵢₖKₖᵤBᵤᵥKᵥₖBₖⱼ>0 occurs in the second-order term. This proves
(6.1). The diagonal of Γ is unchanged. Invertibility on a short perturbation
segment preserves the determinant sign.

For the strict full-ceiling guards, implement Γ_e by decreasing every
off-own singleton reward by e, with own singletons and all nonsingletons
unchanged. The finitely many strict (L),(U) inequalities persist for all
sufficiently small e. The perturbed reward distance is e, and Theorem B
gives exact stationary equilibria of these literal nearby tables.

### 6.2 Strictifying weak half-ceiling guards

For four players labeled as above, preserve every own singleton and Never.
Make exactly these changes:

- Decrease every off-own singleton reward by e.
- In each selected recipient row i=0,1, decrease rᵢ({2,3}) by e.
- In each selected row, decrease every reward whose coalition contains both
  0 and 1 by 3e.
- Leave all other coordinates unchanged.

The reward distance is at most 3e, and its singleton matrix is Γ_e. Each
external-only reward in the lower ranking test decreases by e; every
own-plus-external reward there is unchanged. Thus every weak lower gap
becomes strict.

At partner hazard 1/2 let β=(1−q₂)(1−q₃). The exact changes are

    δQᵢ=−3e/2,  δHᵢ=−e/2,
    δΔᵢ=−e+(3e/4)β≤−e/4.                             (6.2)

For Hᵢ the changed external-only absorption has weight (1−β)/2 and the
changed partner-only absorption has weight β/2. The rewards at partner plus
outsiders without i do not change. The degree-(2,2) Bernstein coefficients
of β are (1−u/2)(1−v/2), all in [0,1]. Thus every weak upper coefficient
decreases by at least e/4 and becomes strict. Theorem B applies for every
sufficiently small e, without any strategic translation of Never.

One may replace the weak Bernstein condition and weak lower ranking by the
actual weak polynomial face guards. At partner zero the same perturbation
changes Δᵢ by e(1−β), strictly positive whenever outsiders are active;
(6.2) strictly lowers the upper face. The weak lower face implies
Γᵢ₂,Γᵢ₃≤0 by its derivatives at zero, so reciprocity again follows from
Γ⁻¹≥0. In this variant use Theorem A directly, with the strict-inverse
index calculation, rather than the Bernstein corollary. The finite linear
tests remain a simpler sufficient adapter.

### 6.3 Returning to one fixed original-game target

If two tables differ by reward distance δ, the same prescribed or deviated
profile has the same terminal outcome law and its payoff changes by at most
δ. Taking the complete response supremum and subtracting prescribed payoff
gives

    |E_r(p)−E_r′(p)|≤2δ.                               (6.3)

Use the perturbed table's exact stationary root in the original game. Its
original complete terminal regret is at most 2e in the first adapter and
6e in the second. Choose e_m↓0 and a convergent subsequence of original
prescribed payoff vectors in the bounded reward cube, with limit v.

Each selected profile still has every αᵢ<1, since rewards do not change
its laws or transitions. Estimate (5.2), now with the original reward bound,
holds whether or not it is Nash for the original table. For a requested
accuracy choose one subsequence member with small original terminal regret
and payoff distance to v; only then choose H₀ using this member's positive
contraction denominators. This gives the required fixed target for every
H≥H₀. Neither a limit of strategies nor continuity of a limiting cap is
used. Theorem C follows.

### 6.4 Weak one-sided full guards without any matrix condition

We prove Theorem D. The weak version of (3.1) gives its lower polynomial
guard; the upper joining differences average to its upper guard. Fix
qₐ=1 and qᵦ=0. For each outsider k∈J and other-outsider hazards z₋ₖ define

    dₖ(z₋ₖ)=Σ_(T⊆J∖{k}) πₖ(T;z)
                  [rₖ({a,k}∪T)−rₖ({a}∪T)].          (6.4)

Here πₖ(T;z) is the independent product probability of the other outsiders
quitting exactly in T. The continuous map z↦clip_[0,1]ᴶ(z+d(z)) has a
fixed point by Brouwer's theorem. It is a mixed Nash equilibrium of the
outsiders' finite joining game: zₖ=0 implies dₖ≤0, zₖ=1 implies dₖ≥0,
and an interior coordinate has dₖ=0. Because a is sure, αₖ=0 and dₖ=Δₖ
for every outsider. Thus all outsider conditions are exactly their original
individual root conditions. The upper weak guard gives Δᵦ≤0, as required
by b's zero hazard.

If z≠0, the lower weak guard gives Δₐ≥0, as required by a's sure hazard.
Every deleted opponent clock contracts: a sees an active outsider, and
every other player sees a sure. Section 5 yields exact stationary terminal
Nash and one fixed uniform payoff, for arbitrary singleton signs.

If z=0, all outsider no-join inequalities follow from their finite-game
Nash conditions, and the upper guard for b at z=0 supplies the remaining
one. Thus

    rₖ({a,k})≤rₖ({a})   for every k≠a.                 (6.5)

The stationary sure-solo profile has value r({a}). If sₐ≥0, a's complete
cap is max(0,sₐ)=sₐ, and (6.5) prices all other replacements, so it is
exact stationary behavioral equilibrium. When sₐ<0, this stationary
conclusion is not automatic.
For sₐ≥0 the same sure-solo profile is also exact Nash at every finite
horizon: delaying cannot increase the owner's nonnegative solo reward,
and all outsiders' absorption remains at date zero. Its payoff delivery
error to r({a}) is at most M/H. Thus the noncontracting nonnegative branch
has the stated uniform conclusion without applying a contraction bound.

For the latter case define the original punishment value

    μₐ=inf_(independent opponent behavioral profiles τ₋ₐ)
                  sup_(complete a-replacements τₐ) Uₐ(τₐ,τ₋ₐ).       (6.6)

Two tracked original-game results supply precisely the needed signed step:

1. `finFour_punishment_le_singleton_of_no_uniformPayoff` in
   `UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`
   states that absence of every original UE payoff implies μᵢ≤sᵢ for all
   four players, on the unchanged signed reward table.
2. `isUniformEquilibriumPayoff_soloReward_of_instantPunishment` in
   `UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean` states
   that μₐ≤sₐ together with (6.5) makes the fixed vector r({a}) a UE
   payoff. Its hypotheses are exactly the owner individual-rationality
   inequality and all outsider no-join inequalities.

For clarity, the latter mechanism prescribes a sure at date zero and every
other player Continue. Only if a refuses does an off-path continuation
punish a. For each positive tolerance a near-optimal independent punishment
plan is selected from the infimum (6.6), or by the stationary punishment
selection theorem in the same source. The owner's continuation cap is at
most sₐ plus tolerance; every other player still encounters a sure owner
unless it joins at date zero, which (6.5) prices. The on-path terminal
payoff is the same vector r({a}) for every tolerance. The cited consumer
provides the complete finite-horizon uniform conclusion, not merely a
terminal payoff calculation.

Now suppose, for contradiction, that the original game has no UE payoff.
The first result gives μₐ≤sₐ, and the second result contradicts that
supposition using (6.5). This proves Theorem D. No punishment plan or
normality hypothesis is assumed by the raw theorem. Outside this contrary
branch, μₐ≤sₐ need not hold and the theorem does not identify its UE target
as r({a}); if μₐ>sₐ, existence instead follows from the first result's
contrapositive. No exact stationary or stationary-approximation conclusion
is inferred in this signed sole-owner branch.

## 7. Half-ceiling example and a full reward neighborhood

Coalition strings denote sets; columns are payoff recipients.

| Coalition | r₀ | r₁ | r₂ | r₃ |
|---|---:|---:|---:|---:|
| 0 | 1 | 3 | −1 | −1 |
| 1 | 4 | 0 | −1 | −1 |
| 01 | 5 | 4 | 178/7 | 2 |
| 2 | 0 | −1 | 0 | 3 |
| 02 | 7/3 | 0 | 8 | −1 |
| 12 | 1 | 83/91 | −2 | 2 |
| 012 | −5 | −6 | 199/7 | −4 |
| 3 | 0 | −1 | 3 | 0 |
| 03 | 2 | 0 | 4 | −4 |
| 13 | 1 | 1 | 3 | 6 |
| 013 | −5 | −6 | 7 | 0 |
| 23 | 0 | −1 | 3 | 0 |
| 023 | 2 | 0 | −5 | 7 |
| 123 | 1 | 1 | 8 | −3 |
| 0123 | −5 | −6 | −3 | −4 |

Here s=(1,0,0,0) and

    Γ = [ 0  3 −1 −1; 3  0 −1 −1;
         −1 −1  0  3; −1 −1  3  0 ],
    Γ⁻¹=(1/15)[2 7 3 3; 7 2 3 3; 3 3 2 7; 3 3 7 2],
    det Γ=45.                                         (7.1)

Both lower ranking margins are one. The two half-ceiling Bernstein arrays
are, with rows and columns indexing the outsider basis,

    c⁰=[−1/2   −1/8    −2;
        −1/12  −49/48  −2;
        −11/6  −23/12  −2],
    c¹=[−1/2     −1/8        −2;
        −99/728  −1563/1456  −2;
        −186/91  −184/91     −2].                       (7.2)

The smallest absolute negative margin is 1/12. Substitution into (2.1)
and (5.1) gives the exact root and full caps

    q=(2/9,1/4,1/3,0),
    Δ(q)=(0,0,0,−271/1944),
    U(q)=B(q)=(3/2,5/13,53/21,15/22).                  (7.3)

Thus the selected hazards are unequal and below one half. Every payoff is
strictly above its own singleton. Joint survival is C=7/18 and opponent
survivals are (1/2,14/27,7/12,7/18). With M=199/7, the quantitative bounds
specialize to horizon-H regret at most 4776/(35H) and censored N-date
regret at most (597/7)(7/12)ᴺ.

Every table at entrywise reward distance δ<1/100 also satisfies the strict
half-ceiling theorem. Indeed its new matrix is Γ+E with ‖E‖∞≤6δ in
induced row-sum norm and ‖Γ⁻¹‖∞=1. Therefore

    ‖(Γ+E)⁻¹−Γ⁻¹‖∞≤6δ/(1−6δ)<2/15.                   (7.4)

All old inverse entries are at least 2/15; the inverse stays strictly
positive, and the perturbation segment remains invertible, retaining the
positive determinant. Lower ranking differences lose at most 2δ. Applying
(3.3) to each of the fifteen coordinate basis rows gives coefficient norms

    [1,3/2,2; 3/2,7/4,2; 2,2,2]                     (7.5)

in reward-coordinate ℓ¹ norm. Thus every upper coefficient loses at most
2δ<1/12. This proves the full sixty-dimensional neighborhood, with no
symmetry preserved or required.

With Γ fixed, recipients 2 and 3 have twenty-two unrestricted nonsingleton
coordinates. The other twenty-two lie in a nonempty open polyhedron defined
by the strict lower and upper tests. All four own-singleton levels can be
arbitrary signed numbers: adding a constant to an entire recipient's
terminal row leaves Γ, Δ, and every displayed raw comparison unchanged.
The theorem applies anew to each such table; this is not strategic
equivalence of arbitrary profiles under terminal-only translations with
Never still zero.

## 8. Exact separation from other raw tests

These comparisons concern the explicit table in Section 7. They are not
claims about every possible previous strategy construction.

A partition with block-replication map E is response-invariant if
Δᵢ(Ex)=Δⱼ(Ex) for all x∈[0,1]ᵏ whenever i,j share a block. Differentiating
at zero gives the necessary block row-sum identities for Γ. Eight of the
fourteen nondiscrete partitions fail these identities: the four partitions
with a three-player block and the four with a cross-pair block 02,03,12,13
and two singleton blocks. In each case the remaining singleton columns
distinguish the block rows by an entry 3 versus −1. The other six have
the following explicit block-constant witnesses; every listed residual
difference is nonzero.

| Partition | q | (i,j) | Δⱼ−Δᵢ |
|---|---|---|---:|
| 01 / 2 / 3 | (0,0,1/2,0) | (0,1) | −115/1092 |
| 12 / 03 | (1/2,0,0,1/2) | (1,2) | 5/16 |
| 02 / 13 | (0,1/2,0,1/2) | (0,2) | 9/8 |
| 0 / 1 / 23 | (0,0,1/2,1/2) | (2,3) | −3/4 |
| 01 / 23 | (0,0,1/2,1/2) | (0,1) | −115/1456 |
| 0123 | (1/2,1/2,1/2,1/2) | (0,1) | −115/2496 |

Thus only the discrete partition is response-invariant, and its matrix is
the full Γ of degree +1. The guarded crossed test applies without any
residual identity or common hazard between the selected players.

Here is a separate comparison with universal raw child-domination tests.
For a nonempty proper child S and outsider k, their unknown weights are
λᵢ≥0, i∈S. For every nonempty A⊆S the rows of Vλ≥b are

    N:   Vᵢ=sᵢ,                         b=sₖ;
    F_A: Vᵢ=sᵢ−rᵢ(A),                  b=sₖ−rₖ(A);
    J_A: Vᵢ=rᵢ(A∪{i})−rᵢ(A),          b=rₖ(A∪{k})−rₖ(A).              (8.1)

The relaxed version permits dropping N when a child singleton is positive.
Every such child test fails for the table. If 0∉S, use outsider 0 and N:
V=0,b=1; no child singleton is positive. For the seven other proper child
sets, these nonnegative row combinations have V≤0 and b>0, making Vλ≥b
impossible even without N. Child coordinates are in increasing order.

| Child S | Outsider | Rows | V | b |
|---|---:|---|---|---:|
| 0 | 1 | J₀ | (0) | 1 |
| 01 | 2 | F₀ | (0,−3) | 1 |
| 02 | 1 | J₀+2F₀₂ | (−8/3,−7) | 1 |
| 012 | 3 | F₀₂ | (−4/3,0,−8) | 1 |
| 03 | 1 | J₀ | (0,−3) | 1 |
| 013 | 2 | J₀₁ | (0,0,−2) | 3 |
| 023 | 1 | J₀+2F₀₂ | (−8/3,−7,−1) | 1 |

This rules out those universal raw certificates, not extension of a
particular child equilibrium: the root (7.3) itself has player 3 Never.

There is no pure terminal equilibrium. In coalition bitmask order 1,...,15,
where player i corresponds to bit 2ⁱ, improving toggle owners are

    1,0,2,0,3,2,0,0,3,2,0,0,2,3,0,

with respective gains

    1,1,3,7/3,8,1,6,2,3,5,6,2,9,5,6.

Every deletion retains a nonempty coalition; singleton coalitions are
defeated by an outside join. These deviations work at the earliest finite
date of any deterministic profile, regardless of hidden later clocks.
All Never is defeated by player 0's positive singleton. The actual payoff
(7.3), being strictly above s in every coordinate, also defeats any proposed
universal terminal payoff exclusion that would require a coordinate or a
nonzero nonnegative weighted average to be at most its singleton benchmark.

## 9. Full-ceiling class and its distinct boundary

The following second table passes the unit-ceiling tests for pair 0,1.

| S | r₀ | r₁ | r₂ | r₃ |
|---|---:|---:|---:|---:|
| 0 | 1 | 4 | 0 | 0 |
| 1 | 4 | 1 | 0 | 0 |
| 2 | 0 | 0 | 1 | 4 |
| 3 | 0 | 0 | 4 | 1 |
| 01 | −3 | −3 | 4 | 2 |
| 02 | 1 | 4 | 4 | −1 |
| 03 | 3 | −1 | 2 | −1 |
| 12 | −3 | 3 | −3 | 3 |
| 13 | −2 | 3 | −2 | 1 |
| 23 | 0 | −2 | 1 | 1 |
| 012 | −4 | 3 | −3 | −2 |
| 013 | −3 | −3 | −4 | −1 |
| 023 | 2 | −3 | 1 | 0 |
| 123 | 0 | 3 | 1 | 1 |
| 0123 | −1 | −5 | −4 | 0 |

It has the same Γ, inverse, and determinant (7.1). Both lower margins are
one. The positive margins rᵢ({j}∪T)−rᵢ({i,j}∪T), for T=∅,2,3,23, are
(7,1,1,1) for recipient 0 and (7,1,2,2) for recipient 1. Its exact root is

    q=(5/7,2/3,1,1),
    Δ(q)=(0,0,1/21,11/21),
    U(q)=B(q)=(0,−19/7,−29/21,2/7).                    (9.1)

The two sure quitters ensure every deleted opponent clock contracts; the
same date-zero product root followed by Never realizes the same payoff and
complete caps. At the all-half hazard vector the residuals are

    (−5/16,−1/32,−23/32,−17/32).                       (9.2)

They are pairwise distinct. This one vector is block-constant for every
partition, so it excludes every nondiscrete response-invariant partition.

The four three-player child LPs (8.1), even with N omitted, have the following
strict certificates. V is in increasing child order.

| Omitted k | Positive row combination | V | b |
|---|---|---|---:|
| 0 | 2F₂+3J₁₂+4F₃+9F₁₂₃ | (−12,−12,−12) | 12 |
| 1 | J₂+F₀₃ | (−1,−1,−1) | 5 |
| 2 | 86J₀+19J₁+22J₀₁ | (−133,−602,−133) | 133 |
| 3 | 5J₁+7F₀₂+2F₀₁₂ | (−25,−25,−28) | 25 |

All these strict conclusions persist throughout reward distance δ<1/1000.
The inverse and raw guards persist by (7.4) and their margin one. At the
all-half vector each Δᵢ changes by at most 7δ/4, since 1−αᵢ=7/8.
The smallest old pairwise separation is 3/16. Each LP row entry changes by
at most 2δ; the four certificate weight sums are 18,2,127,14, giving errors
at most 36δ,4δ,254δ,28δ, respectively, smaller than all required margins.
Thus this is another full-dimensional raw class, not an equality locus.

This neighborhood is not covered by any relabeled weak half-ceiling raw
test. For pair 01, at partner hazard 1/2 and both outsiders sure the
residuals of recipients 0 and 1 are 1/2 and 3/2, respectively, contradicting
even weak nonpositive Bernstein coefficients. Any pair other than 01 or 23
leaves a positive +3 external singleton entry in a selected recipient row,
violating the weak lower ranking test. For pair 23 the lower test fails
because r₂({0,1})=4>s₂=1, also r₃({0,1})=2>s₃=1. The positive half-face
values lose at most 2δ under reward perturbation; each lower violation loses
at most 2δ. All failures persist for δ<1/1000. Thus the two finite upper
test classes are genuinely different, even allowing pair relabeling.

### Why the ceiling and guards are substantive

For the half-ceiling table in Section 7,

    r₀({0,1})−r₀({1})=1,
    r₁({0,1})−r₁({0})=1.

It fails the upper guard at a pure partner for this selected pair. Its
half-ceiling theorem cannot be replaced by a sure-partner argument.
Indeed it fails Theorem D for every ordered pair. Any lower-passing owner
must select its unique positive-singleton partner, so the only possible
unordered pairs are 01 and 23. Pair 01 fails either orientation's upper
test by the two positive joining gains above. For pair 23 the lower test
fails in both orientations, since r₂({0,1})=178/7>s₂=0 and
r₃({0,1})=2>s₃=0. This excludes the matrix-free sixteen-comparison
adapter, not every conceivable sure-owner construction.

Theorem D's sure-owner construction therefore does not replace the
half-ceiling proof. Conversely, for full-ceiling Fin4 UE it removes all
matrix assumptions, needs only one orientation of the guards, and allows
weak signs. It does not replace the stronger interior, at-least-three-active
conclusion of the crossed degree theorem.

Row swapping without guards is invalid. In the table whose only nonzero
coordinate is r₀({0,1})=2, the vector q=(0,1,0,0) has Δ=(2,0,0,0).
The row-swapped unit-cube map fixes q, but original player 0 can join and
gain two. The fixed-point transfer, not determinant arithmetic alone,
excludes this false equilibrium.

## 10. Adapter, existing consumers, and remaining scope

The adapter takes only the raw terminal table and a selected pair. It forms
Γ, its inverse/determinant when using Theorems B or C, and literal lower,
joining, or Bernstein coefficient inequalities. Theorem A then produces
the stationary hazards and their actual value; Section 5 establishes every
complete response cap and the uniform target. Section 6 produces all
approximating roots afresh and selects the weak-boundary target. No strategic
witness remains an unproduced input in these raw classes.

Theorem D instead produces a finite joining Nash root. In its only
noncontracting branch, the named original-table contrary-source theorem and
instant-punishment consumer in Section 6.4 supply the signed completion.
Neither theorem uses a selected favorable root as an input.

The following tracked declarations in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` express the
existing semantic consumer:

- `quittingTerminalPayoff_stationary_eq_of_fixedPoint` identifies the actual
  terminal payoff of a jointly absorbing Bellman fixed point.
- `quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash`
  gives exact complete caps while retaining the boundary condition.
- `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
  and `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
  consume the original root and all-player deleted-clock contraction.

The boundary condition in that source is αᵢ=1 ⇒ max(0,sᵢ)≤vᵢ. It is
vacuous for every root produced by Theorem A. The declarations do not supply
the new crossed root. The ordinary proof above includes the full cap and
uniform estimates independently.

Strict positive inverse and the absence of homogeneous complementary
vectors also correspond to
`noHomogeneousSimplexSolution_of_positive_leftInverse` in
`UniformEquilibrium/Quitting/Classification/LCP/PositiveInverse.lean`.
The integer degree and guarded game-specific root existence are additional
mathematical content, not asserted to be already formalized by that lemma.

A narrow formalization separates the ambient residual expansion, the
common-height crossed clipping map, exclusion of all artificial boundary
roots, the R0 local comparison, global and annular degree, and the original
endpoint adapter. The weak boundary additionally needs (6.1), the literal
reward perturbations, and complete-cap reward robustness. Root existence
must be proved, not stored as a hypothesis of an input structure.

Without any matrix restriction at all, Theorem D says every hypothetical
four-player counterexample must fail its sixteen weak one-sided comparisons
for every ordered pair (a,b). This is a necessary restriction, not a proof
that a passing pair always exists.

Inside the positive-determinant, nonnegative-inverse four-player matrix
region, every hypothetical counterexample must additionally fail the weak
half-ceiling tests for every relabeled pair. More generally, Theorem A
excludes any table passing its explicit guards and crossed R0 degree test.
These assertions are contrapositives of the raw producers; they do not
assert that any remaining table has a suitable pair. No argument here
produces guards for all tables, settles the unrestricted four-player
conjecture, controls a general chronological cap-change problem, or reduces
arbitrary stochastic games to this quitting-game class.

## Reference

[1] M. Seetharama Gowda, *Applications of Degree Theory to Linear
Complementarity Problems*, Mathematics of Operations Research 18(4), 1993,
868–879, Section 2, pp. 869–870. The paper fixes the componentwise-min
convention and states the degree properties and R0 right-hand-side
invariance used here. The guarded quitting-game construction is the proof
in Sections 2–6, not a theorem attributed to that paper.
<https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf>
