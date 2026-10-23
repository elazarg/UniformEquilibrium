# Uniform equilibrium from a contracting Jordan return

A four-player quitting family admits a periodic equilibrium for every
sufficiently small positive crossing parameter. A repeated positive eigenvalue
produces a return of size `n2^−n`, so the construction selects a period with
a logarithmic correction. Each positive-parameter table has a full-dimensional
open UE neighborhood. The limiting table also has a UE with one fixed target.
Complete stationary, sure-first, fixed-pair and specified raw-criterion
comparisons are proved below. No unrestricted nonexistence or general Fin4
closure is asserted.

## 1. The literal family and the conclusion

There are four independent quitting players `I={0,1,2,3}`, one live state,
zero live and Never rewards, and permanent absorption at the first nonempty
quitter coalition. Every actual absorbing reward is `r_i(S)=1+Z_i(S)`.
Own singleton native rewards are zero. For `δ≥0`, set

```
Aδ = [0       1       -6       -1/100]
     [1       0       -3/2     -2/5]
     [-δ     -3/5      0        1]
     [-7/100 -1/25     1        0].
```

Let `f=(01)(23)`. Define `J_i,f(i)=1/100`, `J_ij=−A_ij/2` for crossing
owners `j≠i,f(i)`, and diagonal zero. Put `Γ=A+J`. For distinct owners,

```
Z_i({j})=Γ_ij,             Z_i({i,j})=J_ij.
```

For opponent pairs `B=01,02,03,12,13,23`, respectively assign the signs
`+1,−1,+1,+1,−1,−1`. The smaller outsider receives this sign as `Δ_i(B)`;
the larger receives its negative. Set

```
Z_i(B)=max(0,−Δ_i(B)),     Z_i(B∪{i})=max(0,Δ_i(B)).
```

Finally `Z_i(I\{i})=1` and `Z_i(I)=0`. These rules specify all sixty native
entries. The only varying entries are `Z_2({0})=−δ/2` and
`Z_2({0,2})=δ/2`.

**Producer theorem.** There is `δ*>0` such that every `0<δ<δ*` has an exact
absorbing behavioral Nash equilibrium repeating the support word

```
123 repeated n times, then 023, 023, 012.                    (1)
```

All three scheduled hazards at each phase lie strictly between zero and one.
Every omitted owner strictly prefers Continue. The number of repeated phases
can be chosen so that

```
n = [log(1/δ)+log log(1/δ)]/log 2 + O(1).                    (2)
```

The same cyclic profile has one fixed terminal-payoff vector which is a
uniform-equilibrium payoff against unrestricted behavioral deviations.
For each such δ, a full sixty-dimensional open neighborhood of its actual
reward table also has a UE of the same period. The neighborhood may depend
on δ. No numerical lower bound for δ* is asserted.

## 2. Root maps, literal endpoints and the repeated triple

Use odds `x_i=q_i/(1−q_i)`. A triple support `S` with continuation native
vector `b` has active indifference equations

```
b_i=−A_iu x_u−A_iv x_v+Δ_i({u,v})x_u x_v,    i∈S,            (3)
```

where `{u,v}=S\{i}`. An omitted owner continues. A smooth signed solution
of (3) defines a local map `T_S(b)` by the literal forced-Continue endpoint;
when the odds are positive and all omitted-owner gaps are nonpositive this
is an actual quitting root. Signed neighborhoods below are used only for
implicit-function arguments, not as strategies.

For `S=123`, write its odds `(x,y,w)` in owner order `1,2,3`. Equation (3)
is independent of δ and is

```
b1=3y/2+2w/5+yw,
b2=3x/5−w+xw,
b3=x/25−y−xy.                                              (4)
```

Put

```
α=51/250+b1,  β=3/10−11b2/25+9b3/10,
γ=b1+2b2/5+3b3/2−b2b3,
x=2γ/[β+sqrt(β²+4αγ)],
y=(x/25−b3)/(1+x),          w=(3x/5−b2)/(1−x).             (5)
```

This is a smooth signed root near zero. The exact map is
`T(b0,z)=(h(z)b0+p(z),G(z))`, where `z=(b1,b2,b3)`,

```
D=(1+x)(1+y)(1+w),                  h=1/D,
p=[101x/100−3y−w/200+xw+yw+xyw]/D,
G1=[3y/4+w/5+yw]/[(1+y)(1+w)],
G2=[3x/10+w/100+xw]/[(1+x)(1+w)],
G3=[x/50+y/100]/[(1+x)(1+y)].                               (6)
```

The omitted owner0 has forced-Quit minus prescribed-Continue gap

```
[−x+6y+w/100+xy−xw−yw−xyw−b0]/D.                          (7)
```

These formulas follow by enumerating opponent coalitions. The checker
reconstructs all sixty entries and verifies the exact endpoint identities
symbolically, including the two reset supports.

Introduce coordinates `u=(s,a,g)` by

```
z=(s,15a−15g/4,a+g).                                       (8)
```

Let `G̃` be (6) in these coordinates. Direct exact algebra gives

```
DG̃(0)=L=[1/2      0      0]
          [17/250  1/2    0]
          [0        0   −1/100].                           (9)
```

The linear part of the odds map (5) in these coordinates is

```
(x,y,w)=(10s/3+25a, 2s/15−g, 2s+15g/4).                   (10)
```

Thus the positive eigenvalue `1/2` has one Jordan block of size two.
Its sole cap eigenvector `(0,15,1)` is on the boundary. Positivity of the
smaller favorite odds will come from the generalized coordinate `s`, not
from a nonexistent strictly positive eigenvector.

## 3. Exact entry and local bounds

The scalar boundary interval is

```
I=[746957/10^6,746977/10^6].                                (11)
```

At `δ=0`, define the backward reset
`R0=T023∘T023∘T012`. Its input is `b=(v,0,0,0)`, `v∈I`.
For its first stage set `t=v/6`, `h=3t/[2(1+t)]`. The odds are `(h,0,t)`
on012 and its output is

```
[3t/(1+t), (h/100+3t/4)/((1+h)(1+t)), 0,
 (−7h/200+101t/100)/((1+h)(1+t))].                          (12)
```

For either following023 stage, its input has `b2=0`; set

```
a=b0/6,       k=(b3+a)/(7/100+a).
```

Its odds are `(k,a,0)` and its output is

```
[3a/(1+a), (b1+101k/100−3a/4+ka)/((1+k)(1+a)), 0,
 (7k/200+a/100+ka)/((1+k)(1+a))].                           (13)
```

The boundary zero odds will be opened by δ in Section 6. All other reset
odds are positive. The omitted-owner gaps at the three stages are below
`−7/100`, `−2/5`, `−3/5`, respectively. The active root Jacobian determinants
at these stages are

```
−6(1+t)(3/5+h),             −6(1+k)(7/100+a),              (14)
```

so all three signed reset maps extend smoothly to a common neighborhood.

The exact outward interval computation applies sixty copies of T to (12)--(13)
while propagating first derivatives in v. It verifies all sixty triple roots
have positive odds, their x lies below one, and their omitted-owner gap is
negative. At the resulting entry `(b0,u0)` it proves

```
.7469671 < b0 < .7469674,          |db0/dv| < .01,
1.50·10^−19 < s0 < 1.51·10^−19,  a0 > 10^−18,
||u0||∞ < ε=2·10^−18,           |g0| < 3·10^−25,
||du0/dv||∞ < 2·10^−20.                                  (15)
```

On the full SIGNED box `||u||∞≤10^−6`, `b0∈[.746,.748]`, exact interval
first and second derivatives give

```
||DG̃(u)||∞ < ρ=3/5,
||G̃(u)−Lu||∞ ≤1000||u||∞²,
||odds(u)−linear_odds(u)||∞ ≤1000||u||∞²,
||D_u(hb0+p)||1 <10,          ||D_u h||1<100,
omitted-owner gap <−7/10.                                  (16)
```

The second-order estimates use the multivariable Taylor formula and the
checked sums of absolute Hessian entries divided by two. The outward
computation actually gives bounds below17 and349 for the two remainders;
1000 is retained for simple subsequent estimates. The square-root branch,
all denominators and all interval acceptance inequalities are checked exactly.
No numerical center for a periodic strategy is supplied.

## 4. A uniform C1 Jordan asymptotic with positive smaller odds

Write `u_k=G̃^k(u0)`. Equation (16) gives `||u_k||≤ερ^k` and
`||D G̃^k||≤ρ^k`. Let

```
L_D=[1/2 0;17/250 1/2],      R(u)=G̃(u)−Lu,
(S,A)= (s0,a0)+Σ_{k≥0} L_D^(−k−1) (R_s(u_k),R_a(u_k)).     (17)
```

The inverse satisfies
`||L_D^(−j)||∞=2^j(1+17j/125)`. Since `2ρ²=18/25<1`, this series
converges uniformly with its first derivative on a neighborhood of the
compact entry curve. For the derivative, use `DR(u)=O(||u||)` and
`||D G̃^k||≤ρ^k`; the same summable polynomial times `(18/25)^k` bounds it.
Thus S and A are C1 functions of the entry, and hence of v. Summing the
geometric series explicitly gives

```
||(S,A)−(s0,a0)||∞ ≤11000 ε²,
||(s_k,a_k)−2^−k(S,A+17kS/125)||∞ ≤11000 ε²ρ^(2k),
|g_k|≤100^−k|g0|+3000 ε²ρ^(2k).                            (18)
```

The constant11 in the first two sums bounds
`2/(1−18/25)+(34/125)/(1−18/25)²`; the last constant uses
`1000/(ρ²−1/100)<3000`. These estimates also hold locally with first
derivatives, with a finite local constant, so the normalized asymptotic is C1.

By (15), `S>.9·10^−19` and `A>.9·10^−18`. Combining (10), (16), (18),
and `ρ²<1/2`, every future odds triple has the lower bounds

```
x_k ≥2^−k[10S/3+25A−313000ε²],
y_k ≥2^−k[2S/15−|g0|−6000ε²],
w_k ≥2^−k[2S−4|g0|−35000ε²].                              (19)
```

All three brackets are strictly positive. In particular the error is small
compared with `2^−k`, not merely compared with `k2^−k`; this is what secures
the favorite owners' smaller odds. The local gap bound remains strict.
The passive coordinate changes by at most `10||u_k||`, so its whole future
stays inside `[.746,.748]` and has a limit `Π(b0,u0)`.

The projection is C1 on a signed neighborhood of the entry curve. Indeed
`|h−1|≤100||u||`, and `Σ||u_k||`, `Σ||D G̃^k||` converge uniformly.
The affine passive recurrence and its derivative therefore converge
uniformly. A direct bound from (15)--(16) is

```
|Π−b0| ≤25ε,
|dΠ/dv−db0/dv| <10^−15.                                  (20)
```

For clarity, the derivative estimate follows from the recurrence
`|d_{k+1}|≤(1+100ερ^k)|d_k|+10ηρ^k`, `η=2·10^−20`.
Its products are below `exp(250ε)<2`; summing the derivative increments
gives at most `500ε(|d0|+25η)+25η`, which is below the stated bound.

Consequently the scalar map

```
H(v)=lim_{n→∞}(T^n R0(v,0,0,0))_0                         (21)
```

maps I strictly into itself and has `|H′|<.02`. It has a unique fixed point
`v*∈I`, with `1−H′(v*)≠0`. No value of v* is supplied to the construction.

Define `C(v)=2^60(17/125)S(v)` using the entry after sixty steps. Equations
(18) imply, uniformly with first derivatives near the boundary curve,

```
(T^n R0(v,0,0,0))_{123}/(n2^−n) → C(v)(0,15,1).           (22)
```

The same expansion holds for nearby signed inputs and parameters through
the smooth reset. The exact entry bounds give

```
.352 <15C(v)<.356,               v∈I.                     (23)
```

## 5. Exact finite returns from an integer scale choice

For n large and `τ∈[2,4]`, put `δ=n2^−n/τ` and let
`Rδ=T023,δ∘T023,δ∘T012,δ`. On a bounded signed neighborhood use inputs
`b=(v,δz1,δz2,δz3)`. The scaled return is

```
Φ_n,τ(v,z)=((T^n Rδ(b))_0, (T^n Rδ(b))_{123}/δ).          (24)
```

The smooth reset, (20), and the C1 asymptotic (22) give uniform C1 convergence
on a neighborhood of the prospective fixed points, uniformly in τ:

```
Φ_n,τ(v,z) → (H(v), τ C(v)(0,15,1)).                      (25)
```

In particular the limit is independent of z. The transverse derivative
with respect to z tends to zero: the input factor δ is canceled by the
output factor `1/δ`, leaving the decaying derivative of `T^n`.
The derivative in v converges by the C1 version of (22).

The limit has fixed point `(v*, τ C(v*)(0,15,1))`. The derivative of identity
minus the limit is triangular, with diagonal blocks `1−H′(v*)` and the
three-dimensional identity. It is nonsingular, uniformly on compact
`τ∈[2,4]`. The uniform implicit-function theorem therefore supplies an exact
fixed point of (24) for every sufficiently large n and every such τ. Its
return Jacobian is nonsingular. This uses a compact family of nonsingular
fixed points, not an assumption that the desired finite cycle already exists.

For each sufficiently small δ, there is an integer n with
`2≤n2^−n/δ≤4`: the intervals
`[n2^−n/4,n2^−n/2]` overlap consecutively for n≥2 and cover a punctured
neighborhood of zero. Thus every sufficiently small δ has a finite return.
Taking logarithms of `δ=n2^−n/τ`, with τ bounded above and below, gives (2).

## 6. Opening all zero reset odds and retaining every endpoint

The fixed points in Section 5 satisfy, by (23),

```
.704< z2 <1.424+o(1),       z1=o(1),       z3=z2/15+o(1).  (26)
```

Their boundedness is uniform in τ. The first reset012 has zero boundary
odds for owner1. Differentiating its exact equations (3) at `δ=0` gives

```
x1/δ → α=(z2−h)/(3/5+h).                                  (27)
```

Its owner2 output divided by δ tends to

```
V=[h/2+(3/10+h)α]/(1+h).                                  (28)
```

At the next reset023, owner3's formerly zero odds satisfy

```
x3/δ → β=(k−V)/(1+k).                                     (29)
```

Both are strictly positive exactly when

```
h<z2<U,
U=h+(3/5+h)/(3/10+h)*[(1+h)k−h/2].                        (30)
```

The exact interval bounds over I give `h<.17` and `U>2`.
Equation (26) lies strictly within this window. At the final reset023,
its owner2 input divided by δ is
`V2=[k/2+β/100]/(1+k)`. Since `0<β<k/(1+k)`, its owner3 odds have positive
leading coefficient whenever

```
k2−k/[2(1+k)]−k/[100(1+k)²]>0.                            (31)
```

The checker proves the left side exceeds `2/5` uniformly on I. Every other
reset odds is already strictly positive at δ=0. The three omitted-owner
gaps retain their strict signs from Section 3. The root Jacobians in (14)
ensure the Taylor limits are uniform on the compact scaled-parameter set.

After the reset, the first sixty repeated triple roots remain proper with
strict inactive gaps by continuity. Their resulting entry lies in a common
neighborhood where the strict margins in (15), (19) persist. The entire
remaining triple segment is therefore proper, with strict inactive gaps.
All components of the exact fixed return are now actual probability roots.
Backward composition gives exactly the physical word (1).

## 7. Full behavioral and uniform-payoff consumer; full-dimensional opening

Each phase has three proper active hazards and one omitted owner. Fix any
owner i and remove its randomization. The opponents' survival over the
finite period is strictly below one, independently of i's behavioral
stopping rule. Thus absorption occurs almost surely under every unilateral
behavioral deviation, with a common geometric period bound for that owner.
The native subtraction of the constant one is therefore legitimate for
these terminal comparisons; it is not applied to a positive-probability
Never outcome.

The cyclic continuation vector from the exact return satisfies forced-Quit
and forced-Continue equality for each active owner, and forced-Quit strictly
below forced-Continue for each omitted owner. Prescribed mixing consequently
has the indicated continuation value. Iterating these one-step comparisons
bounds the payoff of every history-dependent randomized unilateral deviation;
the residual continuation term vanishes under the geometric survival bound.
This proves terminal Nash against the full behavioral deviation class.

Let v be this profile's actual terminal-payoff vector. If M bounds the
absolute raw rewards, the expected absorption time against any unilateral
deviation is bounded by the period length divided by one minus that owner's
opponent survival over the period. Hence finite-horizon average rewards
converge uniformly over all unilateral behavioral deviations to their
terminal rewards, with an O(1/T) bound. The same bound holds for the profile.
For every ε>0, all sufficiently large horizons therefore give an ε-Nash
profile with payoff within ε of the SAME v. This is the fixed-target UE
contract, with no horizon-dependent target and no restricted deviation class.

For a fixed sufficiently small positive δ, the period n+3 is finite. Every
active probability is proper, every inactive inequality is strict, and each
local active root Jacobian is nonsingular. The return fixed point has a
nonsingular Jacobian by Section 5. The ordinary implicit-function theorem
therefore continues the whole cycle under arbitrary small independent
perturbations of the sixty absorbing rewards. Strict probabilities,
inequalities and opponent absorption persist. The same complete consumer
then gives a UE for every reward table in a full-dimensional open neighborhood.
The period remains fixed within that neighborhood; no uniform radius as δ→0
is asserted.

## 8. The limiting table has one fixed uniform-payoff target

Let v* be the unique scalar fixed point of H from Section 4. The actual
terminal target of the cycle produced at δ is exactly

```
(1+v_n, 1+δz1, 1+δz2, 1+δz3).
```

The uniform scaled implicit-function construction gives `v_n→v*` and bounded
z as δ decreases to zero, independently of the selected admissible integer n.
These targets therefore converge to the single vector

```
V*=(1+v*,1,1,1).                                          (32)
```

This vector is a UE payoff of the limiting raw table at δ=0. To prove the
fixed-target quantifiers, fix ε>0. Choose one positive δ so small that its
raw table is within ε/4 of the limiting table in sup norm and its target
is within ε/4 of V*. By Section 7 the corresponding fixed cyclic profile,
for all sufficiently large horizons, is ε/4-Nash and has payoff within ε/4
of its own target. Changing the reward table by ε/4 changes any prescribed
or deviating finite-horizon payoff by at most ε/4. Thus its regret in the
limiting game is at most `ε/4+2ε/4=3ε/4`, and its payoff is within
`ε/4+ε/4+ε/4=3ε/4` of V*. The profile may depend on ε; V* does not.

This is a limit-transfer argument for uniform equilibrium. It does not assert
a finite-period exact equilibrium at δ=0 or a full-dimensional open
neighborhood of that endpoint. The uniform comparison gaps below still
exclude stationary and fixed disjoint-pair approximate families there.

## 9. Literal family and statement

Let0≤δ≤1/1000. Four independently randomized players have a single live
state, Boolean Continue/Quit actions, permanent absorption on every nonempty
quitter coalition, and zero live and Never payoff. Actual absorbing rewards
are r_i(C)=1+Z_i(C), with Z_i({i})=0. Favorite pairs are01 and23. Define

```
Aδ = [0       1       -6       -1/100]
     [1       0       -3/2     -2/5]
     [-δ     -3/5      0        1]
     [-7/100 -1/25     1        0].
```

For distinct i,j set J_ij=1/100 if j is i's favorite, and J_ij=−A_ij/2
otherwise. Set Γ=A+J, hence

```
Γδ = [0       101/100 -3       -1/200]
     [101/100 0       -3/4     -1/5]
     [-δ/2   -3/10    0        101/100]
     [-7/200 -1/50    101/100   0].
```

Put Z_i({j})=Γ_ij and Z_i({i,j})=J_ij. For opponent pairs B in the order
01,02,03,12,13,23, assign signs+1,−1,+1,+1,−1,−1. The smaller outside
owner receives that sign as Δ_i(B), the larger its negative. Define
Z_i(B)=max(0,−Δ_i(B)) and Z_i(B+i)=max(0,Δ_i(B)). An opponent triple
pays1 and the grand coalition pays0 in native coordinates. These rules
specify all sixty entries; only Z_2({0})=−δ/2 and Z_2({0,2})=δ/2 vary.

**Comparison theorem.** Over the ENTIRE closed parameter interval:

1. Every stationary prescribed profile has full behavioral terminal
   exploitability bounded below by one fixed positive number.
2. The same holds over all prescribed profiles repeating two fixed disjoint
   pairs, all three partitions, both orders, and all zero/proper/sure hazards.
3. No sure-first root with any arbitrary behavioral continuation is exact Nash;
   its necessary one-date regret has a uniform positive lower bound.
4. All fourteen nondiscrete positively row-scaled response partitions fail.
   The discrete matrix is R0 with degree+1, so it supplies no degree-not-one exit.

The architecture gaps persist in a common sufficiently small full-reward
neighborhood of the parameter interval. Each strictly positive parameter
also has its own raw neighborhood on which the additional direct criteria
in Section15 fail. No gap against arbitrary prescribed behavioral strategies
is asserted; a longer-period equilibrium would be compatible with all these
claims. No minimum possible period or complete classification of equilibria
is inferred.

## 10. Complete uniform stationary exclusion

For stationary hazards q∈[0,1]^4 define, in native coordinates,

```
H_i=∏_(j≠i)(1−q_j),
P_i=Σ_(nonempty B⊆I\{i})Pr_q(B) Z_i(B),
Q_i=Σ_(B⊆I\{i})Pr_q(B) Z_i(B+i),
F_i=(1−H_i)Q_i−P_i.                                (1)
```

At every nonzero stationary Nash profile,

```
q_i>0 ⇒ F_i≥0,       q_i<1 ⇒ F_i≤0.                 (2)
```

Indeed actual prescribed value is
1+[q_i Q_i+(1−q_i)P_i]/[1−(1−q_i)H_i]. Substitution gives forced-Quit
minus Continue endpoint equal to F_i/[1−(1−q_i)H_i]. The denominator
is positive at every nonzero profile. This establishes(2) on every boundary,
not merely in the proper interior. AllNever has actual value0 and immediate
Quit gives1, so it is excluded separately.

### 10.1 The analytic origin cube

Use hazard radius h=1/512. The support census is complete:

* With singleton support{j}, choose an observer i with a fixed Γ_ij<0
  throughout the interval. Its inactive field is
  F_i=q_j(J_ij q_j−Γ_ij)>0, violating(2).
* With support{i,j}, a proper active field equals
  q_j(J_ij q_j−Γ_ij). For a favorite pair Γ_ij=J_ij+1, so it cannot
  vanish. For a crossing pair choose a direction with Γ_ij<0≤J_ij;
  this includes02 atδ=0 by choosing i=0. Again the active field cannot vanish.
* For a triple support, choose its owner i whose favorite is absent. For
  its two active opponents j,k set c=−Γ_ij−Γ_ik and K_i=Z_i({j,k}).
  Both singleton Γ entries are nonpositive. The lower bounds on c and
  the exact K_i, for triples012,013,023,123 respectively, are

  ```
  c≥3/10,11/200,601/200,19/20;       K_i=0,1,1,0.
  ```

  Hence h(c+K_i)<c uniformly. For positive q_j,q_k≤h,

  ```
  P_i/(q_jq_k)
   =Γ_ij(1/q_k−1)+Γ_ik(1/q_j−1)+K_i
   ≤−c(1/h−1)+K_i<0.
  ```

  All participant native rewards are nonnegative, so Q_i≥0. Thus F_i>0,
  contrary to the required equality for this proper active owner. No full
  four-dimensional inverse bound is being applied to a proper triple.
* For full support, F=−Γδ q+Rδ(q). Exact coefficient and inverse bounds are

  ```
  ||Rδ(q)||∞≤K||q||∞²,    K=12687/200,
  ||Γδ^-1||∞≤L=335656892/75578685,
  K L/512=354873249067/644938112000<1.
  ```

  Therefore F=0 forces ||q||∞≤KL||q||∞², impossible for positive
  ||q||∞≤1/512.

These bounds are uniform in δ. Every polynomial coefficient is affine in
δ, so the nonlinear absolute-coefficient sum is convex and bounded by its
endpoint maximum. The determinant and every adjugate entry of Γδ are
strictly positive affine functions at both endpoints. Each inverse row sum
is a fractional linear function of δ, hence has its maximum at an endpoint.
The exact determinant is

```
det Γδ=(94482961−9604750δ)/100000000>0,
min Γ0^-1=717100/94482961>0.
```

The checker verifies all endpoint positivity and coefficient identities
symbolically. The radius1/256 does not satisfy the full-support KL bound; the stated
proof uses radius1/512.

### 10.2 The complete cube

Each F_i has degree at most2 separately in each hazard. For a polynomial
Σ_β a_β q^β, its tensor Bernstein coefficient of multidegree(2,2,2,2) is

```
b_α=Σ_(β≤α)a_β∏_j binom(α_j,β_j)/binom(2,β_j).
```

The polynomial lies in the convex hull of those coefficients. Clear rational
denominators and retain integer arrays at BOTH parameter endpoints. Affine
parameter dependence implies that every intermediate coefficient is the
corresponding convex combination. A closed hazard box is rejected only if
some F_i is strictly negative at all coefficients at both endpoints while
the box has q_i>0, or strictly positive throughout while its box has q_i<1.
Either case contradicts(2). The small origin cube uses Section10.1.

A midpoint split changes a Bernstein coordinate slice(a0,a1,a2) to

```
left=(4a0,2(a0+a1),a0+2a1+a2),
right=(a0+2a1+a2,2(a1+a2),4a2),
```

at four times the previous positive denominator. Every sign test and split
therefore uses Python integers only. Both closed children are retained,
including their common face. A finite node/depth budget can only raise an
error; it never accepts an unresolved box.

The deterministic whole-parameter run terminates with **254557 nodes,
127279 leaves, maximum depth68, and exactly one analytic-origin leaf**.
Every leaf has the stated exact sign or analytic reason. Its union covers
[0,1]^4, including all zero and sure faces. Thus the only point satisfying(2)
is q=0, which was already excluded as an actual Nash profile.

## 11. Complete fixed-pair exclusion

Fix a mate involution m and positive proper hazards q_i. Put p_i=J_i,m and
c_i=J_i,m−Γ_i,m=−A_i,m. At its active phase, owner i's value is p_i q_m.
Its value W_i at the opposite phase satisfies active indifference, giving
W_i=c_i q_m/(1−q_m). For the opposite pair{j,k}, let

```
D=(1−q_j)(1−q_k),
C_i=Γ_ij q_j(1−q_k)+Γ_ik q_k(1−q_j)
    +Z_i({j,k})q_jq_k+p_i q_m D,
Q_i=J_ij q_j(1−q_k)+J_ik q_k(1−q_j)+Z_i({i,j,k})q_jq_k,
E_i=(1−q_m)C_i−c_i q_m,
H_i=(1−q_m)Q_i−c_i q_m.                             (3)
```

Every proper two-pair Nash must satisfy E=0,H≤0. For favorite schedule01|23,
c_i=−1 gives W_i<0 while immediate Quit has nonnegative native reward,
so that schedule is impossible.

For the two crossing schedules E=Γδ q+Rδ(q). With the same L as above,
exact nonlinear bounds give K=4403/200 for02|13 and K=1601/200 for03|12.
In both cases LK/256<1, so the only E-root in[0,1/256]^4 is0. A complete
Bernstein cover, keeping both δ endpoints as in Section10, rejects any other
box when some E row is uniformly strictly signed or some H row uniformly
strictly positive. It terminates with

| Schedule | Nodes | Leaves | Maximum depth |
| --- | ---: | ---: | ---: |
| 02 / 13 | 143 | 72 | 32 |
| 03 / 12 | 691 | 346 | 36 |

Thus E=0,H≤0 implies q=0 on the ENTIRE hazard cube, uniformly across δ.

To pass to all actual fixed-pair profiles, sure hazards are ruled out by
Section12 at their first positive-probability reached occurrence. Assume every
hazard is below1. If both phases are nonempty and one is solo, its sole
proper mixer i has Quit value0 and sees no current opponent quit. Its next
phase value must therefore be0. Immediate Quit at that next phase is
strictly positive if some active opponent j has J_ij>0, because the event
that exactly j quits has positive probability and all participant rewards
are nonnegative. The only potential exception is δ=0,i=2 and opposite
active support exactly{0}. Then owner0 is itself solo in that opposite
phase and the same argument applied to it uses J_02=3>0. Contradiction.

If one phase is empty, a proper two-owner active phase requires
J_ij q_j=Γ_ij for both owners. Favorite Γ_ij=J_ij+1 makes this impossible;
a crossing pair has at least one direction Γ_ij<0≤J_ij, including02 atδ=0.
One sole active owner harms a fixed negative-crossing observer, which can
instead guarantee1 by immediate Quit. AllNever gives0 instead of1. These
cases exhaust every zero/sure pattern. A continuation reached with positive
probability must itself be exact Nash, since a profitable continuation
replacement lifts to a profitable original replacement. Thus the phasewise
arguments have the required actual strategic meaning.

## 12. Uniform punishment and all sure-first faces

Every actual participant reward is at least1 throughout the closed parameter
interval. Immediate Quit therefore guarantees1 against every opponent law.
Opponents choosing Never hold the complete response cap to exactly1. Thus
all true actual punishment values equal1, and every arbitrary off-path
continuation has full cap at least1. Native punishment values are zero.

Changing J while keeping A and every higher contact corner fixed leaves
ALL native endpoint differences g_i identically unchanged. Thus the literal
face formulas below apply to the present Jordan table as well.

For current hazards q, let g_i(q) be native forced-Quit minus forced-Continue
payoff when all-Continue has value0. A root with a sure owner h requires

```
q_i>0 ⇒ g_i≥0,       q_i<1 ⇒ g_i≤0.                 (1)
```

For i≠h, a sure opponent makes the continuation irrelevant. For h, an
arbitrary actual continuation cap b_h≥1 makes its exact Quit-minus-Continue
cap comparison g_h−H_h(b_h−1)≤g_h. Consequently (1) is necessary even
for arbitrary behavioral tails. The following four analyses exhaust the
closed sure boundary.

### Sure owner0

Write x=q1,y=q2,z=q3 and a=δ+(1−δ)x. The opponent gaps are

```
g1=−1+2z(1−y),
g2=a−(1+a)z,
g3=[7−107x+93y(1−x)]/100.                           (2)
```

On the parameter interval0≤a≤1. If y>0, g2≥0 gives z≤a/(1+a)≤1/2.
Then g1<0 forces x=0. Formula(2) makes g3>0, forcing z=1, a
contradiction. Hence y=0. The two remaining opponent gaps are 2z−1 and
(7−107x)/100. Their boundary signs force x,z to be proper, so
x=7/107,z=1/2. At this unique opponent equilibrium,

```
g2=50(δ−1)/107<0,      g0=−13/214<0.
```

Thus the sure owner would withdraw.

### Sure owner1

Write x=q0,y=q2,z=q3. None of the face's gaps depends on δ, because
owner1's sure action prevents the only two changed coalitions from occurring.
The relevant formulas are

```
g0=−1+2y(1−z),
g2=[−12xz+2x+2z+3]/5,
g3=[26(1−x)(1−y)−25]/25.                            (3)
```

If z>0, g3≥0 forces x,y≤1/26. Then g0<0 gives x=0 and g2>0 gives
y=1, contradiction. Hence z=0. Now g2>0 gives y=1, and g0=1 gives
x=1. At this unique opponent equilibrium g1=−1<0.

### Sure owner2

Write x=q0,y=q1,z=q3. All three opponent gaps are independent of δ:

```
g0=6−5y−7z+5yz,
g1=[3−5x−z+xz]/2,
g3=−1+2x(1−y).                                     (4)
```

If x=0, the signs force y=1,z=0, then g0=1 contradicts x=0. If x=1,
they force y=0,z=1, then g0=−1 contradicts x=1. Thus x is proper and
g0=0 yields z=(6−5y)/(7−5y)∈[1/2,6/7]. This makes z proper; g3=0
yields x=1/[2(1−y)] and y<1/2. The case y=0 would give x=1/2,z=6/7
and g1=1/28>0. Hence all three are proper. The remaining equation is
20y²−30y+1=0, with unique admissible root

```
x=(−5+√205)/18, y=(15−√205)/20, z=(22−√205)/9.
```

The sure owner's gap has derivative x(1−y)(1−z)≥0 with respect to δ.
Its maximum on the parameter interval is therefore its value at1/1000:

```
g2≤(170187−12919√205)/18000<0,
12919²·205−170187²=5251000036>0.
```

Thus this owner also withdraws, uniformly across the interval.

### Sure owner3

Write x=q0,y=q1,z=q2. Again every face gap is independent of δ. The
opponent formulas are

```
g0=[101(1−y)(1−z)−100]/100,
g1=[−13xz+3x+3z+2]/5,
g2=−1+2y(1−x).                                     (5)
```

If x>0, g0≥0 gives y,z≤1/101. Then g2<0 forces z=0 and g1>0 forces
y=1, contradiction. Hence x=0; then g1>0 forces y=1 and g2=1 forces
z=1. At this unique opponent equilibrium g3=−1<0.

The four arguments cover every zero, proper and sure opponent pattern.
The exact checker verifies all δ-dependent identities and monotonicity;
(3)--(5) for the opponents are the unchanged literal polynomial expansions.
The compact parameter interval times the four closed sure faces has no point
satisfying(1). The continuous maximum one-date regret consequently has a
strictly positive minimum there. Every complete actual root with a behavioral
tail has at least this regret, since its relevant continuation cap is≥1.
Raw payoff perturbations preserve that strict exclusion by continuity and
the immediate-Quit cap bound1−η. This also excludes every singleton-base
certificate using true punishment, regardless of its free carrier.

## 13. Uniform positive gaps for both architectures

Suppose parameters δ_n in the compact interval and stationary or fixed-pair profiles q_n
had full behavioral terminal exploitability tending to0. Pass to limits
δ_n→δ* and q_n→q*, fixing the architecture and finite schedule choice on a subsequence.

If q* has at least two positive coordinates, every opponent-deleted period
survival is below1. Both the prescribed payoff and full response cap vary
continuously with δ and q there. Indeed if H_i is opponent period survival,
N_i is literal Never value and L_i(t) is the deadline value at first-period
phase t, the corresponding deadline in period k has value

```
(1−H_i^k)N_i+H_i^k L_i(t).
```

Every behavioral stopping law is a mixture of deadlines and Never, so the
full cap is exactly max(N_i,L_i(0)) for a stationary profile and max(N_i,L_i(0),L_i(1)) for a two-phase profile. A zero limiting gap would give
an exact Nash in the fixed architecture atδ*, contrary to Sections10--12.

If q* has only one positive coordinate j, choose a negative crossing observer
whose Γ_ij is fixed across δ. Its prescribed value tends to1+Γ_ij<1,
while immediate Quit guarantees1. Again the gap cannot vanish.

Finally suppose q*=0. Put h_n=sum_i q_ni>0 and take w_n=q_n/h_n→w in
the unit simplex. Uniform bounded rewards and the fixed one-phase or two-phase period give
singleton first-exit masses q_nj+O(h_n²), total collision mass O(h_n²), and
total absorption h_n+O(h_n²). Prescribed actual values therefore tend to
1+(Γδ* w)_i. Immediate Quit≥1 implies y=Γδ* w≥0. A singleton support
is excluded by the preceding fixed negative crossing. Thus every w_i<1.
For w_i>0 the actual Never response tends to
1+y_i/(1−w_i). Vanishing debt and y_i≥0 force y_i=0 on the positive support.
Hence w≥0,y≥0,w_i y_i=0.

This is impossible solely from Γδ*^-1>0. If y=0, invertibility gives w=0.
If y≠0, strict inverse positivity gives w=Γδ*^-1 y strictly positive in
EVERY coordinate, and complementarity then forces y=0. Both contradict
sum_i w_i=1. This argument deliberately avoids assuming the principal02
block is nonsingular atδ=0.

Every possible limiting case is excluded, proving one positive gap d over
the whole closed parameter interval and the union of both architecture families. Changing
raw rewards by at mostη changes every prescribed and deviating terminal
payoff by at mostη, uniformly over every profile; the literal Never payoff
stays0. Thus exploitability changes by at most2η. A uniform raw tube of
radius below d/2 retains positive stationary and fixed-pair gaps. For each fixed strategy,
finite-horizon averages converge to terminal payoffs by bounded convergence,
so this gap also prevents arbitrary-accuracy uniform witnesses within either
architecture.

## 14. Every response quotient and all positive row-weight walls

### 14.1 The fourteen nondiscrete partitions

A literal response-invariant quotient requires proportional stationary
response rows after identifying hazards within each block. Positive recipient
scaling changes a two-row coefficient minor only by a positive factor.
The following exact minors are nonzero throughout0≤δ≤1/1000. Monomial
coordinates follow the displayed block order. For exponents α,β the minor
is coefficient_i(α) coefficient_j(β)−coefficient_i(β) coefficient_j(α).

| Blocks | Rows | α | β | Minor |
| --- | --- | --- | --- | --- |
| 01/2/3 | 0,1 | 001 | 010 | −477/800 |
| 1/02/3 | 0,2 | 001 | 010 | 303/100+δ/400 |
| 1/2/03 | 0,3 | 001 | 010 | −2201/20000 |
| 0/12/3 | 1,2 | 001 | 010 | 327/400 |
| 012/3 | 0,1 | 01 | 10 | −3993/10000 |
| 12/03 | 1,2 | 01 | 10 | 1029/2000−3δ/8 |
| 0/2/13 | 1,3 | 001 | 010 | −217/1000 |
| 02/13 | 0,2 | 01 | 10 | 213/100−201δ/400 |
| 2/013 | 0,1 | 01 | 10 | 1341/800 |
| 0/1/23 | 2,3 | 001 | 010 | 707/2500 |
| 01/23 | 0,1 | 01 | 10 | −41511/20000 |
| 1/023 | 0,2 | 01 | 10 | 101δ/200−593/5000 |
| 0/123 | 1,2 | 01 | 10 | 19δ/40−7171/10000 |
| 0123 | 0,1 | 1 | 2 | 41733/10000 |

The checker enumerates all fifteen partitions and computes every displayed
minor from the literal polynomial fields. For each minor the sum of the
absolute nonconstant coefficients times(1/1000)^degree is smaller than
the absolute constant. This excludes a zero throughout the closed interval,
including the full-block quotient where linear coefficients alone would
not suffice. The actual own offset1 cancels from the zero-discount field F.

The discrete quotient retains Γδ. Strict inverse positivity implies R0:
for w≥0,y=Γw≥0,w_i y_i=0, either y=0 and w=0, or y≠0 and w=Γ^-1 y>0
in every coordinate, again forcing y=0. At offset−1, any complementary
solution has w=Γ^-1(1+y)>0, hence y=0 and w=Γ^-1 1. This unique regular
solution has orientation sign(detΓ)=+1. Thus the R0 degree is+1. The
principal02 block is singular atδ=0, but this proof does not need that block
to be nonsingular. All quotient and degree obstructions persist on a raw
neighborhood of the compact parameter interval by their strict margins.

### 14.2 Arbitrary positive odds, row factors and pair orientations

Choose any positive odds ρ_j and positive C¹ row factors m_i on the cube.
This includes every positive multiaffine or constant weighting. Put

```
ψ_j(u)=ρ_j u_j/[1+(ρ_j−1)u_j],
D_j(u)=1+(ρ_j−1)u_j,
G_i(u)=m_i(u)∏_(j≠i)D_j(u)² F_i(ψ(u)).
```

Choose one favorite pair or both, orienting each as preferred i and partner k,
and let K be the cube with u_i≥u_k on the selected pairs. The ordered-wall
requirement is G_i≥G_k whenever u_i=u_k in K. No such choice can succeed.

Suppose it did. For η>0 let v be1 on preferred owners and0 elsewhere.
Brouwer supplies a fixed point of projection_K(u+G(u)+ηv). Write f=G+ηv.
The fixed-point variational inequality gives ordinary cube complementarity:
at an interior tied pair, feasible increase of i gives f_i≤0 and feasible
decrease of k gives f_k≥0, contradicting f_i≥f_k+η. At a tied zero corner,
f_i≤0 and f_k<f_i; at a tied one corner, f_k≥0 and f_i>f_k. At untied
coordinates the order normal is inactive. Disjoint pairs cause no extra
intersection case. Thus the same complementarity holds at every fixed point.

If a sequence η→0 has a nonzero limiting fixed point, positive factors and
ψ transfer it to a nonzero complementary F point, contradicting Section10.
Suppose instead u_η→0. At zero, DG(0)=−M with
M=diag(m(0)) Γ diag(ρ), so M^-1 is strictly positive and M_ii=0.
Normalize by max(||u_η||∞,η). A subsequential limit w,τ satisfies

```
w≥0 in the ordered cone, τ≥0, max(||w||∞,τ)=1,
Mw≥τv,                 w_i[(Mw)_i−τv_i]=0.           (4)
```

If τ=0, the inverse-positive R0 argument just given forces w=0, impossible.
If τ>0, write Mw=τv+y with y≥0. Since v is nonzero and M^-1>0,
w=M^-1(τv+y) is strictly positive in EVERY coordinate. Hence complementarity
forces Mw=τv.

Choose any selected preferred pair i,k. Differentiating the tied-wall guard
at zero gives(Mw')_i≤(Mw')_k for an ordered vector w' tied on that pair.
Lower w_i to w_k to obtain w'. Restoring w_i leaves row i unchanged because
M_ii=0 and increases row k because the favorite entry M_ki>0. Thus
(Mw)_i≤(Mw)_k. But Mw=τv gives the opposite strict differenceτ. This
contradiction proves noncollapse and excludes every odds, factor and orientation
selection. Unbounded parameters are not a loophole: any single successful
selection would supply this contradiction.

This inverse-positive version does not use strict negativity of every
crossing coefficient. Therefore it remains valid even around theδ=0 table,
provided the stationary gap, inverse positivity and positive favorite entries
persist. Those are strict uniform facts already established. Positive
recipient scales are absorbed into the row factors.

## 15. Remaining direct raw guards

The architecture conclusions already exclude every raw producer whose output
is stationary, sure-first with a punishment tail, or fixed disjoint-pair
period two. In particular they cover every valid sufficiently-large parameter
choice in stationary coalition-jackpot constructions, without estimating an
unspecified threshold. Source-mode reductions with additional semantic-source
hypotheses are not silently treated as raw existence theorems.

For each positive δ, the remaining finite necessary guards fail over all
owner roles, relabelings and positive recipient factors:

* Every J_ij>0. Thus negative participant-pair chambers and rotating templates
  requiring a pair premium−b/2 with b>0 fail. A full four-owner premium core
  is witnessed by favorite pairs01 and23, so conditions requiring greatest
  core size at most three fail. Those disjoint traps also exclude a common
  leaver required to lie in every trap.
* The pure crossing pair03 has both participant premiums positive. It refutes
  the product-low requirement. On that trap both joining differences are
  positive, so neither owner is a support-specific weak leaver. With strictly
  positive trap weights, the coalition{3} gives a strictly positive inserted
  joining sum at owner0, excluding every weighted leaver selection.
* Every triple contains a favorite edge with J−Γ=−1, which violates the
  six-positive-difference guard for a triple collision box. Each Γ column
  has just one positive off-diagonal entry, excluding the joint-positive
  passive triple requirement. Signed inverse-column inactive caps require
  positive opposite-pair premiums to be nonpositive and also fail.
* Any marked-calendar condition requiring nonpositive positively weighted
  participant premium at the first marked block is contradicted by a
  coalition{i,j} with marked i and unmarked j: its sum is λ_i J_ij>0.
  This covers every marking, ordered partition and positive weight choice.
* Every column has a negative crossing, so there is no no-harm singleton.
  Mutual singleton signs are equal and strict for δ>0, so there is no escort
  edge. Atδ=0 the only possible edge is0→2 and there is no directed cycle.
  The balanced-singleton-cycle-to-escort implication therefore excludes all
  balanced singleton certificates, including repeated-owner presentations.

Two parameter inequalities give explicit all-scale screens. If positive row
scales a0,a1 obey opposite-row preference0 over1, its singleton requirements
include a0Γ03≤a1Γ13 and a0Γ01≤a1Γ10. They force a0/a1≥40 and≤1.
The reverse preference requires a1Γ12≤a0Γ02 and a1Γ10≤a0Γ01, forcing
a1/a0≥4 and≤1. Both orientations fail. The more general one-pair or
two-pair positive-weight walls are already excluded by Section14.2.

For bounded-inverse-corner and nonmatching-positive-passive guards, the
computed inactive cap obeys ell_i≤1/(768 U), where U bounds the inverse
entries above. This follows from their defining bounds
ell_i=c_i κ r_min/2, κ≤1/4, r_min≤1/(32 U Q), Q≥3c_i.
After positive recipient scaling a_i, U≥(Γ^-1)_ii/a_i. At recipient3 all
pair premiums are at least a3/100, whereas

```
(Γδ^-1)_33=7575000(5δ+12)/(94482961−9604750δ),
detΓδ·[(Γδ^-1)_33/100−1/768]
 =(300484750δ+603629039)/76800000000>0.                (5)
```

Thus EVERY schedule and recipient role violates the necessary pair cap.
Recipient1's smallest pair premium does not give this contradiction;
(5) uses the required recipient3 row.

### Every literal proper child, including security withdrawals

For a nonempty proper child C and outsider h, allow arbitrary nonnegative
advance weights a_i and withdrawal weights d_i. Necessary future and joining
rows, for every nonempty S⊆C, are

```
−Z_h(S)≤Σ_(i∈C)a_i[−Z_i(S)],
Z_h(S+h)−Z_h(S)
 ≤Σ_(i∈C){a_i[Z_i(S+i)−Z_i(S)]+d_i W_i(S)}.          (6)
```

Here W_i=0 for i∉S, and W_i=Z_i(S−i)−Z_i(S) for nonsingleton S containing
i. For S={i}, it is the chosen actual restart floor minus own singleton1.
The basic zero floor, evaluated-security floor and untruncated terminal-security
floor are all≤1: the security LP has that literal singleton upper constraint,
and its additional zero floor is≤0. Thus W_i≤0 for singleton S, even in the
strongest listed version. No guessed or numerically optimized floor is used.

For singleton child j choose crossing outsider h by0→3,1→2,2→0,3→1.
The joining left side is strictly positive and its right side nonpositive.
For crossing pair children02,03,12,13 use S=C and outsiders3,1,0,2. The
left side is1, advance coefficients vanish identically, and withdrawal
coefficients are the nonpositive crossing A entries. For favorite child01
choose h=2,S={1}: the row is3/5≤−a0+d1(γ1−1)≤0. For favorite child23
choose h=1,S={2}: it is3/2≤−a3+d2(γ2−1)≤0.

Three triple-child joining contradictions are unchanged contact identities:

```
C012,h3,S02: 1≤−a1−6d0−δ d2,
C013,h2,S13: 1≤−a0−(2/5)d1−(1/25)d3,
C023,h1,S03: 1≤−a2−(1/100)d0−(7/100)d3.
```

For the last child C123,h0, add TWICE the future row S12 to the future
row S={2}. The resulting contradiction is

```
3≤−(3/4)a1−(3/5)a2−(301/100)a3≤0.                  (7)
```

The factor two is useful: every resulting coefficient is strictly negative,
so this certificate is robust under small arbitrary raw perturbations even
with unbounded nonnegative weights. All fourteen children are covered;
advance-only and future/join-only certificates are included by setting d=0.
Positive recipient scales divide out at the outsider and are absorbed into
the child weights. For each positive δ, every nonstructural coefficient in
these witnesses has a strict sign, yielding its own full raw neighborhood.
Atδ=0 the coefficient−δ d2 vanishes; the exact family contradiction still
holds, but that row alone does not prove an open full-reward obstruction there.

The standalone pair checker also verifies(5), both order contradictions,
and all fourteen security-child duals at both parameter endpoints, including
the structural-zero conditions for the positive-parameter neighborhood claim.

These comparisons prove separation from the stated architectures and raw
criteria. They do not prove nonmembership in an unspecified maximal
neighborhood or a different equilibrium branch of an earlier local reset
existence theorem. The new Jordan producer must state its analytic parameter
scope directly, without turning this comparison into a minimal-period claim.

## 16. Scope of the new parameter family

On every triple, the present family has transverse spectrum
`(1/2,1/2,−1/100)`, with a one-dimensional eigenspace at1/2. Indeed if the
favorite owners are a,b and the remaining owner is c, then
`J_S+(1/2)A_S` has only its two favorite off-diagonal entries nonzero.
Each equals51/100. Its rank is two, while direct determinant expansion gives
one negative root−1/100 and a double root1/2. The positive cap eigenvector
is proportional to `−A_S e_c`, whose c coordinate is zero. Thus none of the
four triples, under any relabeling or positive recipient scaling, meets a
simple strictly interior positive-eigenvector hypothesis. The Jordan series
in Section 4 supplies the smaller positive odds that such a hypothesis
cannot provide here.

The literal simple-Perron weak-crossing family has favorite ratios `J_ij/A_ij`
with multiset `{1/1000,1/10,1/100,1/10}`. The present family's multiset is
`{1/100,1/100,1/100,1/100}`. These ratios are invariant under positive
recipient scaling, and relabeling merely permutes them. Hence no role or
scale choice identifies the two literal parameter families. This statement
concerns their stated raw recipes; it does not claim exclusion from an
unspecified maximal neighborhood or another branch of a local existence
theorem. The periods constructed here need not be minimal, and no
classification of all periodic equilibria is claimed.

## 17. Complete reproduction and source correspondence

Appendices A, B and C contain the complete standalone checkers. Save them,
respectively, as `jordan_reset_check.py`, `jordan_stationary_check.py` and
`jordan_pair_check.py`, then run

```
python jordan_reset_check.py
python jordan_stationary_check.py
python jordan_pair_check.py
```

Python 3, SymPy and NumPy suffice. No saved cycle, numerical strategy root,
external proof payload or unlisted source import is used. Appendix A verifies
the complete raw endpoint algebra, sixty-step boundary entry, local first
and second derivatives, and strict reset guards with outward 512-bit integer
intervals. Appendix B verifies all origin supports, fourteen quotient minors
and the complete254557-node stationary cube across the parameter interval.
Its optional `--origin-only` is not a complete stationary check. Appendix C
verifies sure faces, both full pair covers, inverse/order bounds and all
fourteen security-child duals. Its optional `--write-certificate FILE.json`
records pair leaves as output, not input. All acceptance tests use exact
rational numbers or integers; floating-point conversion only prints results.

The infinite series, uniform implicit-function arguments, behavioral consumer
and compactification proofs are the mathematical arguments above. A checker
for the displayed finite bounds does not replace those arguments.

The exact game-semantic contracts are `IsεQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/FirstBranch.lean`, and
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.

The native scalar complementarity correspondence is
`stationaryQuittingGain_complementarity_iff_endpoints` in
`UniformEquilibrium/Quitting/Stationary/Gain.lean`. The quotient predicate is
`QuittingResponseInvariantOnUnitCube` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`,
and its discrete degree calculation matches
`r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`.
The complete sure-face comparison covers `QuittingSingletonBaseCertificate`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`.
The exact leaver definitions are `HasProductLowQuittingPremium`,
`HasSupportSpecificQuittingLeavers`, `HasWeightedQuittingTrapLeavers` and
`IsCommonQuittingPremiumLeaver` in the corresponding files under
`UniformEquilibrium/Quitting/Classification/`. The singleton-cycle implication
is `BalancedSingletonCycleCertificate.exists_escortCycle` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`.
The raw quiet-child definitions are `DeadlineWithdrawalRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`,
`DeadlineSecurityRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityMixedRaw.lean`,
and `DeadlineSecurityTerminalRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityTerminalDebt.lean`.
The singleton floor bound is `deadlineWithdrawalSecurityValue_le_singleton`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`.
The results in this manuscript are ordinary mathematical proofs. The
parameterized certificates and asymptotic producer are not asserted to be
Lean-checked instances of those declarations.


## Appendix A. Exact Jordan reset bounds

```python
"""Exact finite bounds for the common-r Jordan reset family.

Python 3 and SymPy. The interval engine uses outward 512-bit integer bounds;
all acceptance assertions use rational/integer arithmetic. Float conversion
is only for printing. No supplied cycle or numerical strategy root is read.
The accompanying note proves the asymptotic return and behavioral consumer.
"""
from fractions import Fraction as F
from math import isqrt
BITS=512;D=1<<BITS
class Iv:
 def __init__(self,lo,hi=None,raw=False):
  if raw:self.lo,self.hi=lo,hi;return
  x=F(lo);self.lo=x.numerator*D//x.denominator;self.hi=-((-x.numerator*D)//x.denominator)
 @classmethod
 def box(cls,c,r):
  a=cls(F(c)-F(r));b=cls(F(c)+F(r));return cls(a.lo,b.hi,True)
 def __add__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);return Iv(self.lo+o.lo,self.hi+o.hi,True)
 __radd__=__add__
 def __neg__(self):return Iv(-self.hi,-self.lo,True)
 def __sub__(self,o):return self+-iv(o)
 def __rsub__(self,o):return iv(o)+-self
 def __mul__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);xs=[a*b for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(xs)//D,-((-max(xs))//D),True)
 __rmul__=__mul__
 def __truediv__(self,o):
  o=iv(o);assert not o.lo<=0<=o.hi,('zero denominator',o.lo,o.hi)
  pairs=[(a*D,b)for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(a//b for a,b in pairs),max(-((-a)//b)for a,b in pairs),True)
 def __rtruediv__(self,o):return iv(o)/self
 def sqrt(self):
  assert self.lo>0
  a=isqrt(self.lo*D);b=isqrt(self.hi*D)
  return Iv(a,b+(b*b<self.hi*D),True)
 def absupper(self):return max(-self.lo,self.hi)
 def lower(self):return float(F(self.lo,D))
 def upper(self):return float(F(self.hi,D))
 def __repr__(self):return str((self.lower(),self.upper()))
def iv(x):return x if isinstance(x,Iv)else Iv(x)
class Jet:
 def __init__(self,v,d=None):self.v=iv(v);self.d=[Iv(0)]*4 if d is None else d
 def __add__(self,o):
  o=jet(o);return Jet(self.v+o.v,[a+b for a,b in zip(self.d,o.d)])
 __radd__=__add__
 def __neg__(self):return Jet(-self.v,[-x for x in self.d])
 def __sub__(self,o):return self+-jet(o)
 def __rsub__(self,o):return jet(o)+-self
 def __mul__(self,o):
  o=jet(o);return Jet(self.v*o.v,[a*o.v+self.v*b for a,b in zip(self.d,o.d)])
 __rmul__=__mul__
 def __truediv__(self,o):
  o=jet(o);v=self.v/o.v
  return Jet(v,[(a-v*b)/o.v for a,b in zip(self.d,o.d)])
 def __rtruediv__(self,o):return jet(o)/self
 def sqrt(self):
  v=self.v.sqrt();return Jet(v,[a/(2*v)for a in self.d])
def jet(x):return x if isinstance(x,Jet)else Jet(x)


def reset(s):
 t=s/6;h=F(3,2)*t/(1+t);D=(1+h)*(1+t)
 b=[3*t/(1+t),(h/100+F(3,4)*t)/D,0,(-F(7,200)*h+F(101,100)*t)/D]
 for _ in range(2):
  a=b[0]/6;k=(b[3]+a)/(F(7,100)+a);D=(1+k)*(1+a)
  b=[3*a/(1+a),(b[1]+F(101,100)*k-F(3,4)*a+k*a)/D,0,(F(7,200)*k+a/100+k*a)/D]
 return b

def tail(b):
 b0,b1,b2,b3=b
 A=F(51,250)+b1;B=F(3,10)-F(11,25)*b2+F(9,10)*b3;C=b1+F(2,5)*b2+F(3,2)*b3-b2*b3
 x=2*C/(B+(B*B+4*A*C).sqrt());y=(x/25-b3)/(1+x);w=(F(3,5)*x-b2)/(1-x)
 D=(1+x)*(1+y)*(1+w)
 out=[(b0+F(101,100)*x-3*y-w/200+x*w+y*w+x*y*w)/D,
     (F(3,4)*y+w/5+y*w)/((1+y)*(1+w)),
     (F(3,10)*x+w/100+x*w)/((1+x)*(1+w)),
     (x/50+y/100)/((1+x)*(1+y))]
 gap=(-x+6*y+w/100+x*y-x*w-y*w-x*y*w-b0)/D
 return out,[x,y,w],gap

def frame(z):
 return [z[0],(4*z[1]+15*z[2])/75,(-4*z[1]+60*z[2])/75]
def unframe(u):
 s,a,g=u;return[s,15*a-F(15,4)*g,a+g]

def entry(mid=F(746967,1000000),width=F(1,100000),n=60):
 p=reset(Jet(Iv(mid)));b=reset(Jet(Iv.box(mid,width),[Iv(1),Iv(0),Iv(0),Iv(0)]))
 p=[x if isinstance(x,Jet)else Jet(x)for x in p];b=[x if isinstance(x,Jet)else Jet(x)for x in b]
 rad=Iv.box(0,width);qmin=Iv(1).lo;gmax=Iv(-1).hi
 for stage in range(n):
  p,_,_=tail(p);old=[x.d[0]for x in b]
  local=[Jet(x.v,[Iv(int(i==j))for j in range(4)])for i,x in enumerate(b)]
  b,qq,g=tail(local)
  for x in b:x.d=[sum((x.d[j]*old[j]for j in range(4)),Iv(0))]+[Iv(0)]*3
  assert all(q.v.lo>0 for q in qq),(stage,qq)
  assert qq[0].v.hi<D
  assert g.v.hi<0,(stage,g.v)
  qmin=min(qmin,min(q.v.lo for q in qq));gmax=max(gmax,g.v.hi)
  for i in range(4):b[i].v=p[i].v+rad*b[i].d[0]
 coords=frame(b[1:]);
 assert F(b[0].v.lo,D)>F(7469671,10000000) and F(b[0].v.hi,D)<F(7469674,10000000)
 assert ab(b[0].d[0])<F(1,100)
 assert F(coords[0].v.lo,D)>F(15,10**20) and F(coords[0].v.hi,D)<F(151,10**21)
 assert F(coords[1].v.lo,D)>F(1,10**18)
 assert max(ab(x.v)for x in coords)<F(2,10**18)
 assert ab(coords[2].v)<F(3,10**25)
 assert max(ab(x.d[0])for x in coords)<F(2,10**20)
 print('entry60',b[0].v,'derivative',b[0].d[0]);print('frame',[(x.v,x.d[0])for x in coords]);print('min odds/gap',float(F(qmin,D)),float(F(gmax,D)))
 return b


class Jet2(Jet):
 def __init__(self,v,d=None,h=None):
  self.v=iv(v);self.d=[Iv(0)]*4 if d is None else d
  self.h=[[Iv(0)for _ in range(4)]for _ in range(4)]if h is None else h
 def __add__(self,o):
  o=hjet(o);return Jet2(self.v+o.v,[a+b for a,b in zip(self.d,o.d)],[[self.h[i][j]+o.h[i][j]for j in range(4)]for i in range(4)])
 __radd__=__add__
 def __neg__(self):return Jet2(-self.v,[-x for x in self.d],[[-x for x in row]for row in self.h])
 def __sub__(self,o):return self+-hjet(o)
 def __rsub__(self,o):return hjet(o)+-self
 def __mul__(self,o):
  o=hjet(o)
  return Jet2(self.v*o.v,[self.d[i]*o.v+self.v*o.d[i]for i in range(4)],[[self.h[i][j]*o.v+self.d[i]*o.d[j]+self.d[j]*o.d[i]+self.v*o.h[i][j]for j in range(4)]for i in range(4)])
 __rmul__=__mul__
 def unary(self,v,a,b):
  return Jet2(v,[a*x for x in self.d],[[a*self.h[i][j]+b*self.d[i]*self.d[j]for j in range(4)]for i in range(4)])
 def inverse(self):return self.unary(1/self.v,-1/(self.v*self.v),2/(self.v*self.v*self.v))
 def __truediv__(self,o):return self*hjet(o).inverse()
 def __rtruediv__(self,o):return hjet(o)*self.inverse()
 def sqrt(self):
  v=self.v.sqrt();return self.unary(v,1/(2*v),-1/(4*v*v*v))
def hjet(x):return x if isinstance(x,Jet2)else Jet2(x)
def ab(x):return F(x.absupper(),D)

def local_check():
 b0=Jet2(Iv.box(F(747,1000),F(1,1000)),[Iv(1),Iv(0),Iv(0),Iv(0)])
 u=[Jet2(Iv.box(0,F(1,1000000)),[Iv(int(j==i+1))for j in range(4)])for i in range(3)]
 out,odds,gap=tail([b0]+unframe(u));g=frame(out[1:])
 norm=max(sum(ab(x.d[j])for j in range(1,4))for x in g)
 hess=max(sum(ab(x.h[i][j])for i in range(1,4)for j in range(1,4))for x in g)/2
 ohess=max(sum(ab(x.h[i][j])for i in range(1,4)for j in range(1,4))for x in odds)/2
 passive=sum(ab(out[0].d[j])for j in range(1,4))
 print('local norm/Hess/oddsHess/passive/gap',float(norm),float(hess),float(ohess),float(passive),gap.v)
 assert norm<F(3,5)
 assert hess<1000 and ohess<1000
 assert passive<10
 hh=1/((1+odds[0])*(1+odds[1])*(1+odds[2]))
 assert sum(ab(hh.d[j])for j in range(1,4))<100
 assert F(gap.v.hi,D)<-F(7,10)


def reset_guards():
 s=Iv.box(F(746967,1000000),F(1,100000));t=s/6;h=F(3,2)*t/(1+t)
 a=t/(2*(1+t));v3=(-F(7,200)*h+F(101,100)*t)/((1+h)*(1+t));k=(v3+a)/(F(7,100)+a)
 U=h+(F(3,5)+h)/(F(3,10)+h)*((1+h)*k-h/2)
 a2=a/(2*(1+a));v33=(F(7,200)*k+a/100+k*a)/((1+k)*(1+a));k2=(v33+a2)/(F(7,100)+a2)
 third=k2-k/(2*(1+k))-k/(100*(1+k)*(1+k))
 print('reset h/U/third',h,U,third)
 assert F(h.hi,D)<F(17,100)
 assert F(U.lo,D)>2
 assert F(third.lo,D)>F(2,5)
 # All three omitted owners' native one-date gaps at the exact boundary roots.
 b=[s,Iv(0),Iv(0),Iv(0)]
 first=(F(7,100)*h-t+h*t)/((1+h)*(1+t))
 assert F(first.hi,D)<-F(7,100)
 bb=reset(s) # Its components are independently checked by the raw table audit.
 b1=(h/100+F(3,4)*t)/((1+h)*(1+t))
 second=(-k+F(3,2)*a-k*a-b1)/((1+k)*(1+a))
 b1b=(b1+F(101,100)*k-F(3,4)*a+k*a)/((1+k)*(1+a))
 last=(-k2+F(3,2)*a2-k2*a2-b1b)/((1+k2)*(1+a2))
 assert F(second.hi,D)<-F(2,5)
 assert F(last.hi,D)<-F(3,5)
 print('reset inactive',first,second,last)


def symbolic_audit():
 import sympy as S
 delta=S.symbols('delta');I=range(4);f=(1,0,3,2)
 A=S.Matrix([[0,1,-6,-S.Rational(1,100)],[1,0,-S.Rational(3,2),-S.Rational(2,5)],[-delta,-S.Rational(3,5),0,1],[-S.Rational(7,100),-S.Rational(1,25),1,0]])
 J=S.Matrix(4,4,lambda i,j:0 if i==j else S.Rational(1,100)if j==f[i]else -A[i,j]/2);Gamma=A+J
 signs={(0,1):1,(0,2):-1,(0,3):1,(1,2):1,(1,3):-1,(2,3):-1};Z={}
 for i in I:
  for mask in range(1,16):
   B=[j for j in I if mask>>j&1 and j!=i]
   if not B:v=0
   elif len(B)==1:v=J[i,B[0]]if mask>>i&1 else Gamma[i,B[0]]
   elif len(B)==2:
    outside=[j for j in I if j not in B];d=signs[tuple(B)]*(1 if i==outside[0]else-1)
    v=max(0,d)if mask>>i&1 else max(0,-d)
   else:v=0 if mask>>i&1 else 1
   Z[i,mask]=S.sympify(v)
 def endpoints(odds,b):
  C=[];Q=[]
  for i in I:
   cn=b[i];qn=S.Integer(0);den=S.prod(1+odds[j]for j in I if j!=i)
   for mask in range(16):
    if mask>>i&1:continue
    w=S.prod(odds[j]for j in I if mask>>j&1)
    if mask:cn+=Z[i,mask]*w
    qn+=Z[i,mask|(1<<i)]*w
   C.append(S.factor(cn/den));Q.append(S.factor(qn/den))
  return C,Q
 b0,x,y,w=S.symbols('b0 x y w')
 b=[b0,S.Rational(3,2)*y+S.Rational(2,5)*w+y*w,S.Rational(3,5)*x-w+x*w,x/25-y-x*y]
 C,Q=endpoints([0,x,y,w],b)
 assert all(S.factor(C[i]-Q[i])==0 for i in (1,2,3))
 D=(1+x)*(1+y)*(1+w)
 expected=[(b0+S.Rational(101,100)*x-3*y-w/200+x*w+y*w+x*y*w)/D,(S.Rational(3,4)*y+w/5+y*w)/((1+y)*(1+w)),(S.Rational(3,10)*x+w/100+x*w)/((1+x)*(1+w)),(x/50+y/100)/((1+x)*(1+y))]
 assert all(S.factor(C[i]-expected[i])==0 for i in I)
 assert S.factor(Q[0]-C[0]-(-x+6*y+w/100+x*y-x*w-y*w-x*y*w-b0)/D)==0
 t=S.symbols('t');h=S.Rational(3,2)*t/(1+t)
 C,Q=endpoints([h,0,t,0],[6*t,0,0,0]);C=[S.factor(v.subs(delta,0))for v in C];Q=[S.factor(v.subs(delta,0))for v in Q]
 assert all(S.factor(C[i]-Q[i])==0 for i in (0,1,2))
 E=[3*t/(1+t),(h/100+S.Rational(3,4)*t)/((1+h)*(1+t)),0,(-S.Rational(7,200)*h+S.Rational(101,100)*t)/((1+h)*(1+t))]
 assert all(S.factor(C[i]-E[i])==0 for i in I)
 a,k,b1=S.symbols('a k b1');C,Q=endpoints([k,0,a,0],[6*a,b1,0,(S.Rational(7,100)+a)*k-a]);C=[S.factor(v.subs(delta,0))for v in C];Q=[S.factor(v.subs(delta,0))for v in Q]
 assert all(S.factor(C[i]-Q[i])==0 for i in (0,2,3))
 E=[3*a/(1+a),(b1+S.Rational(101,100)*k-S.Rational(3,4)*a+k*a)/((1+k)*(1+a)),0,(S.Rational(7,200)*k+a/100+k*a)/((1+k)*(1+a))]
 assert all(S.factor(C[i]-E[i])==0 for i in I)
 AA=A.extract([1,2,3],[1,2,3]);JJ=J.extract([1,2,3],[1,2,3]);V=S.Matrix([[1,0,0],[0,15,-S.Rational(15,4)],[0,1,1]])
 L=V.inv()*(-JJ*AA.inv())*V
 assert L==S.Matrix([[S.Rational(1,2),0,0],[S.Rational(17,250),S.Rational(1,2),0],[0,0,-S.Rational(1,100)]])
 assert -AA.inv()*V==S.Matrix([[S.Rational(10,3),25,0],[S.Rational(2,15),0,-1],[2,0,S.Rational(15,4)]])
 print('PASS literal60 table, exact triple/reset policy endpoints, Jordan matrix and linear odds')

if __name__=='__main__':
 symbolic_audit();entry();local_check();reset_guards()
 print('PASS exact Jordan reset producer bounds; asymptotic and full behavioral claims require accompanying proof')
```

## Appendix B. Complete stationary and quotient audit

```python
"""Uniform stationary and response-quotient audit for the common-r Jordan family.

Python 3, SymPy, NumPy. Standalone: no external source/data imports.
The literal family has actual rewards 1+Z, live and Never reward zero.
Every arithmetic exclusion uses rational numbers or Python integer objects.
Both closed children of every split are retained; endpoint coefficient tests
cover every delta in [0,1/1000] by affine interpolation. Budget exhaustion
raises an error, never a proof result. No unrestricted UE obstruction claimed.
"""
import argparse
import itertools
from fractions import Fraction
import numpy as np
import sympy as s

I=tuple(range(4))
Q=Fraction
q=s.symbols('q0:4')
FAVORITE=(1,0,3,2)

def table(delta):
    R=s.Rational
    A=s.Matrix([[0,1,-6,-R(1,100)], [1,0,-R(3,2),-R(2,5)],
        [-delta,-R(3,5),0,1], [-R(7,100),-R(1,25),1,0]])
    J=s.Matrix(4,4,lambda i,j:0 if i==j else R(1,100) if j==FAVORITE[i] else -A[i,j]/2)
    Gamma=A+J
    z={(i,0):s.S.Zero for i in I}
    for i in I:
        z[i,1<<i]=s.S.Zero
        for j in I:
            if j!=i:
                z[i,1<<j]=Gamma[i,j]
                z[i,(1<<i)|(1<<j)]=J[i,j]
    for pair,sign in zip(itertools.combinations(I,2),(1,-1,1,1,-1,-1)):
        mask=sum(1<<j for j in pair)
        outside=[i for i in I if not mask>>i&1]
        for order,i in enumerate(outside):
            delta=sign*(-1 if order else 1)
            z[i,mask]=s.sympify(max(0,-delta))
            z[i,mask|(1<<i)]=s.sympify(max(0,delta))
    for i in I:
        z[i,15^(1<<i)]=s.S.One
        z[i,15]=s.S.Zero
    assert len(z)==64
    return z

def fields(z):
    H=[];P=[];QQ=[]
    for i in I:
        pp=qq=0
        for mask in range(16):
            if mask>>i&1:continue
            w=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in I if j!=i)
            pp+=z[i,mask]*w
            qq+=z[i,mask|1<<i]*w
        H.append(s.prod(1-q[j] for j in I if j!=i))
        P.append(s.expand(pp));QQ.append(s.expand(qq))
    F=[s.Poly(s.expand((1-H[i])*QQ[i]-P[i]),*q)for i in I]
    g=[s.expand(QQ[i]-P[i])for i in I]
    return H,F,g

def coefficients(polys):
    assert len(polys)==8
    assert all(poly.degree(q[j])<=2 for poly in polys for j in I)
    raw=[]
    for poly in polys:
        for alpha in itertools.product(range(3),repeat=4):
            value=sum(v*s.prod(s.binomial(alpha[j],mon[j])/s.binomial(2,mon[j])
                        for j in I) for mon,v in poly.terms()
                        if all(mon[j]<=alpha[j] for j in I))
            raw.append(s.sympify(value))
    denominator=int(s.ilcm(*(s.denom(v)for v in raw)))
    arr=np.array([int(v*denominator)for v in raw],dtype=object).reshape(8,3,3,3,3)
    return denominator,arr

def split_coefficients(b,axis):
    # Both child arrays represent their exact polynomials at FOUR TIMES
    # the parent's positive common denominator. Thus all sign tests below
    # use integers only; no interval rounding or tolerance is involved.
    v=np.moveaxis(b,axis+1,-1)
    a0,a1,a2=v[...,0],v[...,1],v[...,2]
    middle=a0+2*a1+a2
    left=np.stack((4*a0,2*(a0+a1),middle),axis=-1)
    right=np.stack((middle,2*(a1+a2),4*a2),axis=-1)
    return np.moveaxis(left,-1,axis+1),np.moveaxis(right,-1,axis+1)

def certify(polys,max_nodes=2000000,max_depth=120):
    denominator,b=coefficients(polys)
    stack=[([Q(0)]*4,[Q(1)]*4,b,0)]
    nodes=leaves=depthmax=origin=0
    while stack:
        lo,hi,b,depth=stack.pop()
        nodes+=1;depthmax=max(depthmax,depth)
        if nodes%100000==0:print("Progress nodes",nodes,"stack",len(stack),"depth",depth,flush=True)
        if max(hi)<=Q(1,512):
            leaves+=1;origin+=1;continue
        witness=False
        for i in I:
            # Rows i and i+4 are the two parameter endpoints. Each
            # intermediate Bernstein coefficient is their convex blend.
            row=np.concatenate((b[i].flatten(),b[i+4].flatten()))
            if (lo[i]>0 and max(row)<0) or (hi[i]<1 and min(row)>0):
                witness=True;break
        if witness:
            leaves+=1;continue
        if nodes>=max_nodes or depth>=max_depth:
            raise RuntimeError('Unexcluded box after budget: '+str({
                'nodes':nodes,'depth':depth,'lo':lo,'hi':hi}))
        widths=[hi[i]-lo[i]for i in I]
        choices=[i for i in I if widths[i]==max(widths)]
        axis=choices[depth%len(choices)]
        left,right=split_coefficients(b,axis)
        middle=(lo[axis]+hi[axis])/2
        lower=lo.copy();lower[axis]=middle
        upper=hi.copy();upper[axis]=middle
        stack.append((lower,hi,right,depth+1))
        stack.append((lo,upper,left,depth+1))
    assert nodes==2*leaves-1
    assert origin==1
    print('PASS: uniform entire Jordan stationary cube',nodes,'nodes',leaves,'leaves',depthmax,'depth',origin,'origin',flush=True)

def partitions(items):
    if not items:
        yield ()
        return
    first,*rest=items
    for part in partitions(rest):
        yield ((first,),)+part
        for j,block in enumerate(part):
            yield part[:j]+((first,)+block,)+part[j+1:]

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--origin-only',action='store_true')
    parser.add_argument('--max-nodes',type=int,default=2000000)
    parser.add_argument('--max-depth',type=int,default=120)
    args=parser.parse_args()
    d=s.Symbol('delta',real=True);dmax=s.Rational(1,1000)
    z=table(d);H,F,g=fields(z)
    assert len(z)==64
    assert z[2,1]==-d/2 and z[2,5]==d/2
    assert all(not value.has(d)for key,value in z.items()if key not in((2,1),(2,5)))
    assert all(s.Poly(f.as_expr(),d).degree()<=1 for f in F)
    Gamma=s.Matrix([[z[i,1<<j]for j in I]for i in I])
    J=s.Matrix([[z[i,(1<<i)|(1<<j)]if i!=j else 0 for j in I]for i in I])
    A=Gamma-J
    endpoints=[]
    for dd in (s.S.Zero,dmax):
        zz={key:value.subs(d,dd)for key,value in z.items()}
        FF=[s.Poly(f.as_expr().subs(d,dd),*q)for f in F]
        GG=Gamma.subs(d,dd);JJ=J.subs(d,dd)
        assert all(zz[i,m]>=0 for i in I for m in range(1,16)if m>>i&1)
        assert all(FF[i].coeff_monomial(1)==0 for i in I)
        assert all(FF[i].coeff_monomial(q[j])==-GG[i,j]for i in I for j in I)
        KK=max(sum(abs(v)for mon,v in f.terms()if sum(mon)>=2)for f in FF)
        BB=GG.inv();LL=max(sum(BB.row(i))for i in I)
        assert min(BB)>0
        endpoints.append((zz,FF,GG,JJ,KK,LL))
    # Determinant and every adjugate entry are affine in delta and
    # strictly positive at both endpoints, hence throughout the interval.
    for matrix in (Gamma,A):
        det=s.expand(matrix.det());adj=matrix.adjugate()
        assert s.Poly(det,d).degree()<=1
        assert all(s.Poly(v,d).degree()<=1 for v in adj)
        assert all(det.subs(d,dd)>0 and min(adj.subs(d,dd))>0 for dd in (0,dmax))
    print("Gamma determinant",s.factor(Gamma.det()),"inverse min at0",min(Gamma.subs(d,0).inv()),flush=True)
    assert min(A.subs(d,0).inv())==s.Rational(40,773)
    K=max(e[4]for e in endpoints);L=max(e[5]for e in endpoints)
    # Coefficient absolute sums are convex in delta. Each inverse row
    # sum is a positive affine/affine quotient, monotone or constant.
    assert K*L/512<1
    for owner in I:
        other=next(i for i in I if all(e[2][i,owner]<0 for e in endpoints))
        for zz,FF,GG,JJ,KK,LL in endpoints:
            t=s.Symbol('t')
            got=FF[other].as_expr().subs({q[i]:t if i==owner else 0 for i in I})
            assert s.expand(got-t*(JJ[other,owner]*t-GG[other,owner]))==0
            assert JJ[other,owner]>0
    for i,j in itertools.combinations(I,2):
        for zz,FF,GG,JJ,KK,LL in endpoints:
            assert GG[i,j]<0 or GG[i,j]>JJ[i,j]>0
            t=s.Symbol('t')
            got=FF[i].as_expr().subs({q[h]:t if h==j else 0 for h in I})
            assert s.expand(got-t*(JJ[i,j]*t-GG[i,j]))==0
    for support in itertools.combinations(I,3):
        owner=next(i for i in support if FAVORITE[i]not in support)
        j,k=[h for h in support if h!=owner]
        for zz,FF,GG,JJ,KK,LL in endpoints:
            cross=-GG[owner,j]-GG[owner,k];passive=zz[owner,(1<<j)|(1<<k)]
            assert GG[owner,j]<=0 and GG[owner,k]<=0 and passive>=0
            assert (cross+passive)/512<cross
    print('PASS: uniform all-support origin; K=',K,'L=',L,'KL/512=',K*L/512)
    print('PASS: Gamma and A inverses strictly positive throughout [0,1/1000]')
    count=0;invariant=[]
    for part in partitions(list(I)):
        ts=s.symbols('t:'+str(len(part)))
        sub={q[i]:ts[j]for j,block in enumerate(part)for i in block}
        polys=[s.Poly(ff.as_expr().subs(sub),*ts)for ff in F]
        witness=None
        for block in part:
            for i,j in itertools.combinations(block,2):
                monoms=sorted(set(polys[i].monoms())|set(polys[j].monoms()),key=lambda a:(sum(a),a))
                for aa,bb in itertools.combinations(monoms,2):
                    minor=s.expand(polys[i].coeff_monomial(aa)*polys[j].coeff_monomial(bb)
                        -polys[i].coeff_monomial(bb)*polys[j].coeff_monomial(aa))
                    if minor.subs(d,0)!=0:
                        witness=(i,j,aa,bb,minor);break
                if witness:break
            if witness:break
        if witness:
            minor=s.Poly(witness[-1],d);constant=minor.coeff_monomial(1)
            print("Quotient minor",part,witness,flush=True)
            # This simple exact perturbation bound rules out a zero on
            # the WHOLE closed parameter interval, not only near zero.
            remainder=sum(abs(c)*dmax**mon[0]for mon,c in minor.terms()if mon[0]>0)
            assert remainder<abs(constant)
            count+=1
        else:
            invariant.append(part)
    assert count==14 and invariant==[((0,),(1,),(2,),(3,))]
    print('PASS: all15 partitions;all14 nondiscrete coefficient minors nonzero uniformly')
    print('PASS: discrete Gamma has positive inverse/determinant;R0 degree+1')
    if not args.origin_only:
        certify(endpoints[0][1]+endpoints[1][1],args.max_nodes,args.max_depth)
    print('SCOPE: stationary prescribed profiles and response quotients only;no UE gap claim')

if __name__=='__main__':main()
```

## Appendix C. Complete pair, sure-face and raw-dual audit

```python
"""Uniform exact proper alternating-pair exclusion for the common-r Jordan family.

Python 3, SymPy, NumPy. All proof arithmetic is rational or Python integer.
All sixty rewards and proof rules are supplied here; no data files are read.
Optional --write-certificate PATH records every exact dyadic leaf.
This excludes proper four-owner two-pair Nash, not arbitrary equilibria.
"""
import argparse
import itertools
import json
from fractions import Fraction
import numpy as np
import sympy as s

I=range(4)
delta_parameter=s.symbols("delta_parameter",real=True)
A=s.Matrix([[0,1,-6,-s.Rational(1,100)],
 [1,0,-s.Rational(3,2),-s.Rational(2,5)],
 [-delta_parameter,-s.Rational(3,5),0,1],
 [-s.Rational(7,100),-s.Rational(1,25),1,0]])
FAVORITE=(1,0,3,2)
J=s.Matrix(4,4,lambda i,j:0 if i==j else s.Rational(1,100) if j==FAVORITE[i] else -A[i,j]/2)
Gamma=A+J
q=s.symbols('q0:4')
SIGNS={(0,1):1,(0,2):-1,(0,3):1,(1,2):1,(1,3):-1,(2,3):-1}

def table():
    z={}
    for i in I:
        for mask in range(1,16):
            opp=[j for j in I if mask>>j&1 and j!=i]
            if not opp:
                value=0
            elif len(opp)==1:
                value=J[i,opp[0]] if mask>>i&1 else Gamma[i,opp[0]]
            elif len(opp)==2:
                outside=[j for j in I if j not in opp]
                delta=SIGNS[tuple(opp)]*(1 if i==outside[0] else -1)
                value=max(0,delta) if mask>>i&1 else max(0,-delta)
            else:
                value=0 if mask>>i&1 else 1
            z[i,mask]=s.sympify(value)
    return z

def fields(z,mate):
    equations=[];gaps=[]
    for i in I:
        j,k=[a for a in I if a not in(i,mate[i])]
        m=mate[i];p=J[i,m];c=-A[i,m]
        passive=z[i,(1<<j)|(1<<k)]
        joining=z[i,(1<<i)|(1<<j)|(1<<k)]
        D=(1-q[j])*(1-q[k])
        C=(Gamma[i,j]*q[j]*(1-q[k])+Gamma[i,k]*q[k]*(1-q[j])
           +passive*q[j]*q[k]+p*q[m]*D)
        Q=J[i,j]*q[j]*(1-q[k])+J[i,k]*q[k]*(1-q[j])+joining*q[j]*q[k]
        equations.append(s.Poly(s.expand((1-q[m])*C-c*q[m]),*q))
        gaps.append(s.Poly(s.expand((1-q[m])*Q-c*q[m]),*q))
    for i in I:
        assert equations[i].total_degree()<=4
        assert equations[i].coeff_monomial(1)==0
        for j in I:
            assert equations[i].coeff_monomial(q[j])==Gamma[i,j]
    assert all(p.degree(variable)<=2 for p in equations+gaps for variable in q)
    return equations,gaps

def coefficients(polys):
    raw=[]
    for p in polys:
        for alpha in itertools.product(range(3),repeat=4):
            raw.append(sum(value*s.prod(s.binomial(alpha[j],mon[j])/s.binomial(2,mon[j])
                           for j in I)for mon,value in p.terms()
                           if all(mon[j]<=alpha[j]for j in I)))
    denominator=int(s.ilcm(*(s.denom(v)for v in raw)))
    arr=np.array([int(v*denominator)for v in raw],dtype=object).reshape(16,3,3,3,3)
    return denominator,arr

def split(b,axis):
    v=np.moveaxis(b,axis+1,-1)
    a0,a1,a2=v[...,0],v[...,1],v[...,2]
    mid=a0+2*a1+a2
    left=np.stack((4*a0,2*(a0+a1),mid),axis=-1)
    right=np.stack((mid,2*(a1+a2),4*a2),axis=-1)
    return np.moveaxis(left,-1,axis+1),np.moveaxis(right,-1,axis+1)

def certify(z,mate):
    equations,gaps=fields(z,mate)
    assert all(s.Poly(p.as_expr(),delta_parameter).degree()<=1 for p in equations+gaps)
    ends=[s.S.Zero,s.Rational(1,1000)]
    # Every inverse entry has a positive affine numerator and one common
    # positive affine denominator. Each row sum is fractional linear, so
    # its supremum on this parameter interval is at an endpoint.
    determinant=s.expand(Gamma.det());adjugate=Gamma.adjugate()
    assert s.Poly(determinant,delta_parameter).degree()<=1
    assert all(s.Poly(v,delta_parameter).degree()<=1 for v in adjugate)
    assert all(determinant.subs(delta_parameter,d)>0 for d in ends)
    assert all(v.subs(delta_parameter,d)>0 for v in adjugate for d in ends)
    L=max(sum(Gamma.subs(delta_parameter,d).inv().row(i))for d in ends for i in I)
    # Coefficient absolute-value sums are convex in the parameter.
    K=max(sum(abs(v.subs(delta_parameter,d))for mon,v in p.terms()if sum(mon)>=2)
          for p in equations for d in ends)
    origin_radius=Fraction(1,256)
    assert L*K/256<1
    endpoints=[s.Poly(p.as_expr().subs(delta_parameter,d),*q)
               for d in ends for p in equations+gaps]
    den,b=coefficients(endpoints)
    stack=[(b,(Fraction(0),)*4,(Fraction(1),)*4,'')]
    leaves=[];nodes=0;maxdepth=0
    while stack:
        b,lo,hi,path=stack.pop();nodes+=1;maxdepth=max(maxdepth,len(path))
        reason=None;bound=None;index=None
        if max(hi)<=origin_radius:
            reason='analytic_origin'
        else:
            flat=b.reshape(16,-1)
            mins=[min(min(flat[i]),min(flat[8+i]))for i in range(8)]
            maxs=[max(max(flat[i]),max(flat[8+i]))for i in range(8)]
            for i in I:
                if mins[i]>0:
                    reason,index,bound='equation_positive',i,int(mins[i]);break
                if maxs[i]<0:
                    reason,index,bound='equation_negative',i,int(maxs[i]);break
            if reason is None:
                for i in I:
                    if mins[4+i]>0:
                        reason,index,bound='inactive_gap_positive',i,int(mins[4+i]);break
        if reason is not None:
            leaves.append({'path':path,'reason':reason,'index':index,'integer_bound':bound,
                           'denominator':den*4**len(path),'lo':list(map(str,lo)),
                           'hi':list(map(str,hi))})
            continue
        if len(path)>=100 or nodes>1000000:
            raise RuntimeError('Unresolved box: no proof accepted at a stopping budget')
        axis=max(I,key=lambda i:hi[i]-lo[i]);mid=(lo[axis]+hi[axis])/2
        left,right=split(b,axis)
        lo1=list(lo);lo1[axis]=mid
        hi0=list(hi);hi0[axis]=mid
        stack.append((right,tuple(lo1),hi,path+'1'))
        stack.append((left,lo,tuple(hi0),path+'0'))
    assert nodes==2*len(leaves)-1
    return {'mate':mate,'L':str(L),'K':str(K),'origin_radius':str(origin_radius),
            'nodes':nodes,'maxdepth':maxdepth,'leaves':leaves}

def sure_faces(z):
    gaps=[]
    for i in I:
        value=0
        for mask in range(16):
            if mask>>i&1:continue
            w=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in I if j!=i)
            value+=(z[i,mask|(1<<i)]-(z[i,mask] if mask else 0))*w
        gaps.append(s.factor(value))
    x,y,w=s.symbols('x y w')
    f0=[s.expand(g.subs(dict(zip(q,(1,x,y,w)))))for g in gaps]
    assert s.expand(f0[1]-(-1+2*w*(1-y)))==0
    a=delta_parameter+(1-delta_parameter)*x
    assert s.expand(f0[2]-(a-(1+a)*w))==0
    assert s.expand(f0[3]-(7-107*x+93*y*(1-x))/100)==0
    assert s.simplify(f0[0].subs({x:s.Rational(7,107),y:0,w:s.Rational(1,2)}))==-s.Rational(13,214)
    assert s.simplify(f0[2].subs({x:s.Rational(7,107),y:0,w:s.Rational(1,2)}))==(50*delta_parameter-50)/107
    for owner in (1,3):
        assert all(s.diff(g.subs(q[owner],1),delta_parameter)==0 for g in gaps)
    assert all(s.diff(g.subs(q[2],1),delta_parameter)==0 for i,g in enumerate(gaps)if i!=2)
    radical=s.sqrt(205)
    point={q[0]:(-5+radical)/18,q[1]:(15-radical)/20,q[2]:1,q[3]:(22-radical)/9}
    upper=s.simplify(gaps[2].subs(point).subs(delta_parameter,s.Rational(1,1000)))
    assert s.simplify(upper-(170187-12919*radical)/18000)==0
    assert 12919**2*205-170187**2>0
    assert s.expand(s.diff(gaps[2],delta_parameter)-q[0]*(1-q[1])*(1-q[3]))==0
    print('PASS all parameter-dependent sure-face identities; remaining faces unchanged')

def raw_guards(z):
    d=delta_parameter;ends=(s.S.Zero,s.Rational(1,1000));B=Gamma.inv()
    margin=s.factor(Gamma.det()*(B[3,3]/100-s.Rational(1,768)))
    assert s.simplify(margin-(300484750*d+603629039)/76800000000)==0
    assert all(margin.subs(d,t)>0 for t in ends)
    assert all(J[3,j]>=s.Rational(1,100) for j in (0,1,2))
    assert Gamma[1,3]/Gamma[0,3]==40
    assert Gamma[0,2]/Gamma[1,2]==4
    assert Gamma[1,0]/Gamma[0,1]==Gamma[0,1]/Gamma[1,0]==1
    checked=0
    for mask in range(1,15):
        child=[i for i in I if mask>>i&1]
        if len(child)==1:
            j=child[0];h={0:3,1:2,2:0,3:1}[j];S=mask
        elif len(child)==2:
            h={3:2,5:3,9:1,6:0,10:2,12:1}[mask]
            S={3:2,12:4}.get(mask,mask)
        elif mask==14:
            # Twice future S12 plus future S2 gives a strict dual,
            # including all nonnegative advance weights without bounds.
            lhs=-2*z[0,6]-z[0,4]
            coeff=[-2*z[i,6]-z[i,4]for i in child]
            assert lhs==3 and coeff==[-s.Rational(3,4),-s.Rational(3,5),-s.Rational(301,100)]
            checked+=1;continue
        else:h,S={7:(3,5),11:(2,10),13:(1,9)}[mask]
        lhs=z[h,S|(1<<h)]-z[h,S]
        advance=[z[i,S|(1<<i)]-z[i,S]for i in child]
        withdrawal=[s.S.Zero if not S>>i&1 or S==(1<<i)
                    else z[i,S^(1<<i)]-z[i,S]for i in child]
        assert all(s.Poly(v,d).degree()<=1 for v in [lhs]+advance+withdrawal)
        assert all(lhs.subs(d,t)>0 for t in ends)
        assert all(v.subs(d,t)<=0 for v in advance+withdrawal for t in ends)
        # At positive delta the only zero coefficients are structural
        # membership zeros or the universal singleton floor upper bound0.
        assert all(v.subs(d,ends[1])<0 or S>>i&1 for i,v in zip(child,advance))
        assert all(v.subs(d,ends[1])<0 or not S>>i&1 or S==(1<<i)
                   for i,v in zip(child,withdrawal))
        checked+=1
    assert checked==14
    print('PASS uniform inverse-corner/order obstructions and all14 literal security-child duals')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-certificate')
    args=parser.parse_args();z=table();sure_faces(z);raw_guards(z)
    friendly=(1,0,3,2)
    assert all(-A[i,friendly[i]]==-1 for i in I)
    records=[certify(z,mate)for mate in ((2,3,0,1),(3,2,1,0))]
    if args.write_certificate:
        with open(args.write_certificate,'w')as out:json.dump(records,out,indent=2)
    for r in records:
        print('PASS uniform delta[0,1/1000]',r['mate'],r['nodes'],'nodes',len(r['leaves']),'leaves',
              'depth',r['maxdepth'],'K',r['K'],'L',r['L'])
    print('PASS complete proper two-pair parameter cube; semantic zero/sure cases require the accompanying proof')

if __name__=='__main__':main()
```
