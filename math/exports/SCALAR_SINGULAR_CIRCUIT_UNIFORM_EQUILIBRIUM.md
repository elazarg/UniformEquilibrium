# A scalar reward criterion for singular-circuit uniform equilibria

## 1. Exact statement, game semantics and strategic inputs

Let I={0,1,2,3}. For each nonempty S⊆I let r(S)∈ℝ⁴ be an arbitrary
finite reward vector. There is one live state. At a live date each player
chooses Continue or Quit, using independent private randomization. If
every player continues, play remains live. Otherwise the set S of that
date's quitters determines the absorbing state. The live date selecting
S pays zero; subsequent absorbing dates pay r(S). A play that never
absorbs pays zero throughout. Actions and states are publicly observed.
No correlation device, public sunspot or hidden continuation controller
is added.

Write Uᵢ(σ) for the expected terminal reward, taking zero on nonabsorption,
and Bᵢ(σ) for the supremum against every unilateral behavioral deviation.
Then Bᵢ≥Uᵢ. While the game is live the publicly observed history is the
unique all-Continue history. Consequently a unilateral behavioral
deviation, including private memory and randomization, induces a law
on its complete stopping clock in ℕ∪{Never}. No finite-clock or
stationary restriction is imposed on Bᵢ.

The following reward-only class is defined by the finite strict
coefficient inequalities in Section 5, using the rational expressions
in Sections 2–4 and the fixed interval [1/40,13/500].

**Theorem.** Every real four-player reward table in that class has one
fixed vector V such that, for every ε>0, there is an independent
periodic behavioral profile σ with

    ∀i,  0≤Bᵢ(σ)−Uᵢ(σ)≤ε,       ‖U(σ)−V‖∞≤ε.

Both joint absorption and absorption by each player's opponents occur
almost surely under σ. The vector V is a uniform-equilibrium payoff
in the original game: for every ε>0 one can choose a profile and a
finite horizon threshold such that, at every larger horizon, every
unilateral behavioral deviation gains at most ε and the prescribed
average payoff is within ε of V. The target V is fixed before ε;
the period and horizon threshold may depend on ε.

The class contains the literal rational table in Section 6, an open
neighborhood in all 60 reward coordinates, and more strongly an open
chamber in 46 specified coordinates times an unrestricted ℝ¹⁴ factor
as enumerated in Section 7. Own-singleton signs need not be positive
for the class theorem. This is a special-case existence producer, not
a proof for every four-player table or a completeness theorem for
periodic strategies.

### Root notation

At one independent root let q∈[0,1]⁴, c(q)=∏ⱼ(1−qⱼ), and

    μ_q(S)=∏_{j∈S}qⱼ ∏_{j∉S}(1−qⱼ),
    F(v,q)=c(q)v+Σ_{S≠∅}μ_q(S)r(S).

For player i and T⊆I∖{i} define

    μ_{−i,q}(T)=∏_{j∈T}qⱼ ∏_{j∈I∖(T∪{i})}(1−qⱼ),

    hᵢ(q)=∏_{j≠i}(1−qⱼ),
    Qᵢ(q)=Σ_{T⊆I∖{i}} μ_{−i,q}(T) rᵢ(T∪{i}),
    Rᵢ(q)=Σ_{∅≠T⊆I∖{i}} μ_{−i,q}(T) rᵢ(T),
    Cᵢ(v,q)=Rᵢ(q)+hᵢ(q)vᵢ,
    gᵢ(v,q)=Qᵢ(q)−Cᵢ(v,q).

Thus Fᵢ=qᵢQᵢ+(1−qᵢ)Cᵢ. A full root Nash condition is

    qᵢ=0 ⇒ gᵢ≤0;  0<qᵢ<1 ⇒ gᵢ=0;  qᵢ=1 ⇒ gᵢ≥0.

These conditions include every quiet player. They concern a binary
root against a payoff annotation v, not a conditional-tail equilibrium.

### Conjecture-facing change and production chain

The new content is a finite raw reward criterion producing a closed
continuation circuit with three convergent ladders and two literal
roots, followed by a literal full-response construction. Closure is
not a field assumed of the reward class. The scalar intermediate-value
step produces it. Every infinite ladder row is full Nash by finite
factored inequalities, including near its binding endpoint.

The strategic inputs are produced as follows: the scalar parameter is
produced by opposite endpoint signs; rates and matching ports are the
displayed rational functions; all active and quiet inequalities are
proved in Section 5; finite truncations and periodic chronology are
constructed in Section 8; deleted-opponent survival, every full cap,
and the fixed target are proved there. Only the terminal-to-uniform
semantic consumer in Section 10 is reused. No minimizer, punishment
law, chosen reply, positive-gap premise, or equilibrium-selection
hypothesis is required.

## 2. Raw data and the fixed scalar interval

Let r be ANY finite signed four-player reward table, with Never0. Write
sᵢ=rᵢ({i}), rᵢ,j=rᵢ({j}), and rᵢ,jk=rᵢ({j,k}); longer subscripts
denote the corresponding unordered set. Own-singleton signs need NOT
be positive for this direct construction. Set

    I_Y=[1/40,13/500],       m=51/2000,       ρ=1/2000.

The intended forward predecessor itinerary is solo0 ladder, solo3
ladder, literal solo1, literal triple123, pair02 ladder. This itinerary
is fixed; its rates and all ports are derived from the REWARD DATA.
Actual chronological periods reverse finite truncations of the whole
list, not just each ladder separately.

The finite scalar criterion in Section 5 is sufficient for the fixed-payoff
uniform equilibrium stated in Section 1. It permits signed rewards,
noncontractive return maps, multiple zeros and the unused coordinates
identified in Section 7. No true minimum, punishment,
equilibrium selection, positive-gap premise, all-tail Nash
assumption or chosen terminal clock is an input.

## 3. Triple rates derived from membership gains

Use the actual joins in triple123:

    d₁₂=r₁,12−r₁,2,    d₁₃=r₁,13−r₁,3,
    d₁,23=r₁,123−r₁,23,
    d₂₁=r₂,12−r₂,1,    d₂₃=r₂,23−r₂,3,
    d₂,13=r₂,123−r₂,13,
    d₃₁=r₃,13−r₃,1,    d₃₂=r₃,23−r₃,2,
    d₃,12=r₃,123−r₃,12.

Define A₂=r₂,12−s₂ and C₃=s₃−r₃,1. Require A₂,C₃>0. For Y∈I_Y
form the following RATIONAL functions of the raw rewards and Y:

    Z=−d₁₂Y/(d₁₃+d₁,23Y),
    D_X=C₃(d₂₁+d₂,13Z)+A₂(d₃₁+d₃,12Y),
    X=−(C₃d₂₃Z+A₂d₃₂Y)/D_X,
    p=−(d₃₁X+d₃₂Y+d₃,12XY)/C₃,
    x=X/(1+X),       y=Y/(1+Y),       z=Z/(1+Z).        (1)

Require d₁₃+d₁,23Y>0, D_X>0, X,Z>0 and 0<p<1 THROUGHOUT I_Y.
Then x,y,z are strictly between0 and1. Let q=(0,x,y,z), c=(1−x)(1−y)(1−z)
and compute Qᵢ(q),Rᵢ(q) directly from r by opponent-product averaging.
For the annotation

    U=(u₀,s₁,s₂+A₂p,s₃−C₃p),                         (2)

the three active gaps, divided by deleted survivals, are

    g₁/h₁=d₁₂Y+d₁₃Z+d₁,23YZ,
    g₂/h₂=−A₂p+d₂₁X+d₂₃Z+d₂,13XZ,
    g₃/h₃=C₃p+d₃₁X+d₃₂Y+d₃,12XY.

All three vanish IDENTICALLY by (1). Thus no active Nash equation
is still an existence premise. The only triple test left is the ONE
quiet gap Q₀−R₀−cu₀≤0, which will be a finite scalar inequality.
The triple head coordinates1,2,3 are exactly Q₁,Q₂,Q₃.

## 4. Linear elimination and scalar closure

For pair02 set

    A₀=r₀,02−s₀,    C₀=s₀−r₀,2,     D₀=A₀+C₀,
    B₂=s₂−r₂,02,    C₂=r₂,0−s₂,     E₂=B₂+C₂,
    H=C₀C₂+A₀C₂+B₂C₀.                               (3)

Require A₀,B₂,C₀,C₂>0. Put a=s₂−Q₂(q) and require 0<a<1 on I_Y.
For a formal pair excess t, let

    Δ(t)=(1+t/C₀)(1+a/C₂),
    Pᵢ(t)=Qᵢ+(a/C₂)rᵢ,0
       +t[rᵢ,2/C₀+a(B₂rᵢ,0/(C₂H)+A₀rᵢ,2/(C₀H)+rᵢ,02/H)]

for i=1,3. The pair ladder's exact corner returns are
b=P₁(t)/Δ(t), d=P₃(t)/Δ(t). These formulas are linear-fractional
in t; they include all passive singleton AND pair rewards.

For the two solo ladders put

    L₀₃=s₃−r₃,0,       L₁₃=s₁−r₁,3,
    J₂₁=r₂,12−r₂,1,     m₂=s₂+J₂₁p/(1−p).

Require L₀₃,L₁₃,J₂₁>0. Define the AFFINE-in-t expressions

    D_s(t)=(r₁,0−r₁,3)[P₃(t)−r₃,0Δ(t)]
            +L₀₃[P₁(t)−r₁,0Δ(t)],
    N_s(t)=(r₂,0−r₂,3)[P₃(t)−r₃,0Δ(t)]
            +L₀₃(s₂−r₂,0)Δ(t),
    E(t)=(r₂,3−m₂)D_s(t)+L₁₃N_s(t).

Let e₀=E(0), e₁=∂E/∂t. Require e₁>0 on I_Y and set

    t=−e₀/e₁,
    b=P₁(t)/Δ(t),       d=P₃(t)/Δ(t),
    λ₀=L₀₃/(d−r₃,0),
    λ₃=L₁₃(d−r₃,0)/D_s(t)·Δ(t),
    u₀=(1−p)[r₀,3+λ₃(s₀−r₀,3)]+p r₀,1.           (4)

The displayed λ₃ uses D_s with the pair denominators cleared; equivalently

    λ₃=L₁₃(d−r₃,0)/[(r₁,0−r₁,3)(d−r₃,0)
                           +L₀₃(b−r₁,0)].

These are all reward-derived rational functions of Y. Require t>0,
b>s₁,d>s₃, D_s(t)>0 on I_Y. The favorite2 equation is ALREADY solved
by E(t)=0, not assumed at a later chosen port.

Indeed the exact two-solo endpoints from V=(s₀,b,s₂,d) are

    V₁,ᵢ=rᵢ,0+λ₀(Vᵢ−rᵢ,0),
    V₂,ᵢ=rᵢ,3+λ₃(V₁,ᵢ−rᵢ,3).                      (5)

Their active/favorite coordinates are V₁,₀=s₀,V₁,₃=s₃ and
V₂,₁=s₁,V₂,₃=s₃. Substitution gives

    V₂,₂=r₂,3+L₁₃N_s(t)/D_s(t)=m₂.

Hence the literal solo1 rate p is exactly the favorite2 indifference
rate against V₂. Its head is exactly U in (2): favorite2 has
U₂=Q₂(solo1)=s₂+A₂p, and quiet3 has U₃=s₃−C₃p.

Only the owner0 corner return remains unsolved. Form

    Ψ(Y)=t−c u₀−R₀(q)+s₀.                           (6)

Require Ψ(1/40)<0<Ψ(13/500). Continuity then supplies a zero Y*∈I_Y.
At this zero W₀=c u₀+R₀=s₀+t, so the triple head is the EXACT
pair-ladder input (s₀+t,Q₁,s₂−a,Q₃). Equations (3–4) return
it to (s₀,b,s₂,d). ALL five ports now match. No contraction or
chosen root accuracy enters this production.

## 5. Finite reward-only criterion and uniform root inequalities

In addition to the strict interval conditions above require the following
RAW constant comparisons:

    r₃,03>s₃>r₃,0,       r₁,13>s₁>r₁,3,
    r₁,0>s₁,             r₁,01<r₁,0,
    r₀,3>s₀,             r₀,03<r₀,3,
    r₂,23<r₂,3,          r₀,01<r₀,1,
    r₃,13<r₃,1,          s₂>r₂,1.                    (7)

These comparisons are all strict at the table in Section 6. The two solo
favorite rates
adapt at EVERY row to the current favorite annotation, not to an old
fixed numerical rate. Their excess contraction factors are respectively
(r₃,03−s₃)/(r₃,03−r₃,0) and
(r₁,13−s₁)/(r₁,13−r₁,3), strictly between0 and1.

### Exact ladder formulas underlying the criterion

For a solo host h with favorite j, suppose its current annotation has
v_h=s_h, v_j=s_j+e with e>0, and

    L=s_j−r_j,h>0,       A=r_j,hj−s_j>0.

Set q_h=e/(A+L+e) and all other rates to zero. The host ties, and the
favorite's gap is −(1−q_h)e+q_h(A+L)=0. Its new excess is
e′=Ae/(A+L+e), bounded by [A/(A+L)]e. Hence charges are summable,
all rates are strictly between zero and one, and the annotations
converge. Every other coordinate updates toward its passive singleton
r_i,h with the same continuation multiplier. The total surviving
multiplier and endpoint are exactly

    λ=L/(v_j−r_j,h),       v_i^end=r_i,h+λ(v_i−r_i,h).

The endpoint formula follows from the favorite's limiting value s_j
and the shared multiplier; geometric decay gives a convergent positive
product. Applied to (h,j)=(0,3) and (3,1), it gives λ₀,λ₃ in Section 4.
The full quiet inequalities below ensure these are full Nash ladders,
not just active/favorite solutions.

For pair02 at annotation (s₀+t,v₁,s₂−a,v₃) set

    q₀=a/(E₂+a),       q₂=t/(D₀+t),       q₁=q₃=0.

Its active gaps are q₂D₀−(1−q₂)t=0 and
(1−q₀)a−q₀E₂=0. Its active heads give

    t′=A₀t/(D₀+t),       a′=B₂a/(E₂+a).

Both excesses decay geometrically. Telescoping these two recursions
gives total survival C=1/[(1+t/C₀)(1+a/C₂)]. If P₀,P₂,P₀₂ are
the terminal coalition weights of the forward affine composition,
the two active endpoint equations and total mass equation are

    C₀P₂−A₀P₀₂=Ct,
    C₂P₀−B₂P₀₂=Ca,
    P₀+P₂+P₀₂=1−C.

Their unique solution is (8), since H>0. Consequently every quiet
endpoint is C times its starting annotation plus P₀r_i,0+P₂r_i,2+
P₀₂r_i,02, which is precisely Pᵢ(t)/Δ(t) in Section 4.
At every later row the remaining ladder has the same quiet endpoint,
so reversing this identity expresses its current annotation in terms
of that endpoint and the current t_n,a_n. Substitution in its quiet
gap gives the polynomial in (9). This proves the uniform formula
for the actual entire ladder.

### Full quiet coverage

Full quiet coverage follows by finite endpoint facts:

- Solo0 quiet1 starts at b>s₁, is pulled toward r₁,0>s₁ and has
  strictly negative nonempty joining gap. Quiet2 starts EXACTLY at
  s₂, is pulled toward r₂,0>s₂ and has gap −E₂<0.
- Solo3 quiet0 starts EXACTLY at s₀, is pulled toward r₀,3>s₀
  and has strictly negative joining gap. Quiet2 stays between V₁,₂
  and V₂,₂, both strictly above s₂. The former follows from C₂>0,
  λ₀<1; the latter from V₂,₂=m₂ and J₂₁,p>0. Its joining gap is
  strictly negative. Positive λ₀,λ₃<1 follow from b>s₁,d>s₃
  and (7), not from a separate infinite-row hypothesis.
- At literal solo1, quiet0 has V₂,₀>s₀ and negative joining gap.
  Quiet3 starts at s₃ and has negative joining gap. Owner1 ties,
  and favorite2 ties by the exact linear elimination.
- Require the triple quiet0 gap Q₀−R₀−cu₀<0 on I_Y. Its three
  active owners already tie identically by Section 3.

For the pair ladder use its exact terminal weights

    C=1/[(1+t/C₀)(1+a/C₂)],       P₀₂=Cta/H,
    P₀=C[a/C₂+B₂ta/(C₂H)],
    P₂=C[t/C₀+A₀ta/(C₀H)].                            (8)

The active excess recursion t′=A₀t/(D₀+t), a′=B₂a/(E₂+a)
contracts geometrically. For i=1,3 set Bᵢ=b,d respectively and

    δᵢ,0=rᵢ,0i−rᵢ,0,
    δᵢ,2=rᵢ,2i−rᵢ,2,
    δᵢ,02=rᵢ,02i−rᵢ,02,
    ℓ₀=sᵢ−Bᵢ,
    ℓ_t=(rᵢ,2−Bᵢ)/C₀+δᵢ,2/D₀,
    ℓ_a=(rᵢ,0−Bᵢ)/C₂+δᵢ,0/E₂,
    ℓ_ta=−Bᵢ/(C₀C₂)+B₂rᵢ,0/(C₂H)+A₀rᵢ,2/(C₀H)
          +rᵢ,02/H+δᵢ,02/(D₀E₂).

Require throughout I_Y

    ℓ₀<0,      ℓ_a<0,      ℓ_t<0,      ℓ_t+ℓ_ta<0.    (9)

At every finite pair stage its actual normalized quiet gap is
ℓ₀+ℓ_t tₙ+ℓ_a aₙ+ℓ_ta tₙaₙ. Since 0<aₙ<1, (9) makes
it strictly negative for ALL n, including arbitrarily late rows near
the active binding endpoint. It does not assume that initial quiet
ports are above their own singletons. This is the finite UNIFORM
quiet proof needed to persist under general table perturbation.

Precise finite coefficient test. All functions in Sections 2–5 are rational
expressions derived from finitely many raw reward entries. Require each
ORIGINAL denominator to have the displayed positive sign; cancellation
of a removable singularity does not waive this requirement. For any
additional rational inequality f(Y)>0, write f=N/D with D positive
on I_Y and expand each polynomial at m:

    N(m+e)=Σ nⱼeʲ,        D(m+e)=Σ dⱼeʲ.

It suffices to check the TWO finite coefficient inequalities

    n₀>Σ_{j≥1}|nⱼ|ρʲ,       d₀>Σ_{j≥1}|dⱼ|ρʲ.       (10)

Apply this to all interval inequalities in Sections 2–5, and to both ℓ_t
and ℓ_t+ℓ_ta as stated; no max or universal semialgebraic oracle is
needed. Endpoint signs of Ψ are exact rational substitutions. For
real rather than rational tables the same finite inequalities still
define a legitimate mathematical class; rationality is needed only
for a fully exact machine arithmetic certificate. Denominator clearing
uses the actual current table, without reusing a derivative estimate
from another table.

Define the raw coefficient class to consist exactly of tables satisfying
the constant strict comparisons, the two endpoint signs, and (10) for
the stated interval signs, with each original denominator checked
separately. This definition refers only to finitely many reward entries
and polynomial coefficients. It does not quantify over a strategy,
a chosen continuation port or an equilibrium. It is enough to use any
fixed polynomial numerator/denominator clearing of the displayed raw
expressions for which these tests hold.

The criterion is therefore a finite REWARD-ONLY sufficient UE producer.
Its hypotheses are coefficient inequalities and literal reward gaps,
not the existence of a closed word. IVT supplies Y*, all five exact
Nash pieces are then explicit, and the finite truncation compiler yields
absorbing terminal approximate Nash at every accuracy with the ONE
fixed payoff V(Y*). The proof retains all full behavioral caps as proved in
Section 8: two fixed positive suppliers0,3 make every deleted period survival
uniformly less than1, and scalar companion fixed points price Never
and every later deadline. No ω+ω chronology, charge-only substitute
for deleted survival, or restricted equilibrium is inferred.

## 6. A complete rational table satisfying the criterion

All own-singleton rewards are 1 and the absolute reward bound is 5.
Each vector lists recipients in the order 0,1,2,3. Never pays zero.

| Coalition S | r(S) |
| --- | --- |
| {0} | (1,3,3,0) |
| {1} | (4,1,−1,−1) |
| {2} | (0,2,1,2) |
| {3} | (4,−2,0,1) |
| {0,1} | (−2,−2,5,5) |
| {0,2} | (3/2,5,−2,5) |
| {0,3} | (−2,5,5,3/2) |
| {1,2} | (5,−2,3/2,5) |
| {1,3} | (5,3/2,5,−2) |
| {2,3} | (5,5,−2,−2) |
| {0,1,2} | (4,4,4,−4) |
| {0,1,3} | (4,4,−4,4) |
| {0,2,3} | (4,−4,4,4) |
| {1,2,3} | (−4,4,4,4) |
| {0,1,2,3} | (−5,−5,−5,−5) |

For this table, (1) simplifies to

    Z=8Y/(7−2Y),
    X=4Y(23−2Y)/(63−57Y+2Y²),
    k=p/2=2Y(43−18Y)/(63−57Y+2Y²).

Writing Qᵢ and R₀ as the literal triple averages, let a=1−Q₂ and

    B_n(t)=Q₁+3a/2+(2+7a/4)t,
    D_n(t)=Q₃+(2+a)t,       Δ(t)=(1+t)(1+a/2).

The linear favorite return equation reduces to

    E*(t)=4D_n(t)−B_n(t)−3Δ(t)
            −k[33D_n(t)+3B_n(t)−21Δ(t)]=0.

The linear-elimination coefficient e₁ is ∂E*/∂t divided by1−2k, so both are
positive on I_Y. Taking t=−E*(0)/(∂E*/∂t), b=B_n(t)/Δ(t),
d=D_n(t)/Δ(t), T=33d+3b−21 gives u₀=4−45d/T. The resulting
Ψ=t−cu₀−R₀+1 is a rational function with numerator and denominator
degrees16. Its endpoint values satisfy EXACTLY

    Ψ(1/40)<0<Ψ(13/500).                              (11)

The following complete rational verifier checks the WHOLE interval,
not samples. It has no numerical root premise, optimization or floating
comparison. Its simplified expressions are the actual current-table
denominator clearing; their nonzero denominators are separately checked.

```python
import sympy as s
Y,t,e=s.symbols('Y t e')
Z=8*Y/(7-2*Y)
X=s.factor(4*(Y+2*Z)/(9-Y-4*Z))
k=s.factor(Y+(1+Y)*X/4)
x=s.factor(X/(1+X)); y=Y/(1+Y); z=s.factor(Z/(1+Z))
p=2*k; c=s.factor((1-x)*(1-y)*(1-z))
Q1=1-3*y+z/2+s.Rational(11,2)*y*z
Q2=1+x/2-3*z+s.Rational(11,2)*x*z
Q3=1-3*x-3*y+9*x*y
a=s.factor(1-Q2)
R0=4*x*(1-y)*(1-z)+4*z*(1-x)*(1-y)+5*(
    x*y*(1-z)+x*z*(1-y)+y*z*(1-x))-4*x*y*z
Q0=c-2*x*(1-y)*(1-z)+s.Rational(3,2)*y*(1-x)*(1-z)
Q0+=-2*z*(1-x)*(1-y)+4*(x*y*(1-z)+x*z*(1-y)
    +y*z*(1-x))-5*x*y*z
BN=Q1+3*a/2+(2+7*a/4)*t
DN=Q3+(2+a)*t; Den=(1+t)*(1+a/2)
NN=s.factor(4*DN-BN-3*Den)
TT=s.factor(33*DN+3*BN-21*Den)
E=s.factor(NN-k*TT)
coef=s.factor(s.diff(E,t))
tt=s.factor(-E.subs(t,0)/coef)
b=s.factor(BN.subs(t,tt)/Den.subs(t,tt))
d=s.factor(DN.subs(t,tt)/Den.subs(t,tt))
T=s.factor(33*d+3*b-21); N=s.factor(4*d-b-3)
u0=s.factor(4-45*d/T)
g0=s.factor(Q0-R0-c*u0)
psi=s.factor(tt-c*u0-R0+1)
mid=s.Rational(51,2000); rho=s.Rational(1,2000)
def polybound(f):
    P=s.Poly(s.expand(f.subs(Y,mid+e)),e)
    terms=P.as_dict(); cc=terms.get((0,),s.S.Zero)
    err=sum(abs(co)*rho**j[0] for j,co in terms.items() if j[0])
    return cc-err,cc+err
def iv(f):
    n,q=s.fraction(s.factor(f)); ql,qh=polybound(q)
    if qh<0: n,q,ql,qh=-n,-q,-qh,-ql
    assert ql>0
    nl,nh=polybound(n)
    vals=[nl/ql,nl/qh,nh/ql,nh/qh]
    return min(vals),max(vals)
for f,lo,hi in [(X,0,1),(Z,0,1),(p,0,1),(tt,0,2),
    (a,0,1),(b,1,3),(d,1,3),(T,0,100),(N,0,5),
    (u0,1,4),(g0,-10,0)]:
    ll,hh=iv(f); assert ll>lo and hh<hi
for f in [7-2*Y,9-Y-4*Z,coef,1-p,1+x,1+y,1+z,
          s.Rational(7,2)-Y,
          s.Rational(9,2)-2*Z-Y/2,5*d+b-3]:
    ll,hh=iv(f); assert ll>0
for BB,aa,bb in [(b,s.Rational(1,2),s.Rational(19,20)),
                 (d,s.Rational(3,10),s.Rational(1,5))]:
    for f in [BB-1, BB/2-aa, BB+s.Rational(2,3),
              3*BB/2-bb]:
        ll,hh=iv(f); assert ll>0
ll,hh=iv(s.fraction(psi)[1]); assert hh<0
assert psi.subs(Y,s.Rational(1,40))<0
assert psi.subs(Y,s.Rational(13,500))>0
```

The interval bounds produced by exact coefficient arithmetic include
1.501<b<1.527,1.374<d<1.400, .914<t<1.004,
.060<a<.063, 1.826<u₀<1.915 and −1.171<g₀<−1.092.
These displayed short decimal enclosures are rational widened bounds,
not approximate root evidence. The base pair quiet coefficients satisfy
(9) uniformly already from b>3/2,d>13/10. All original denominator
signs follow from the checked positive factors and the explicit positive
table constants; e₁=coef/(1−p)>0. The circle can therefore be closed
by IVT directly, using only the stated scalar coefficient test.

## 7. Fourteen independent arbitrary reward coordinates

The support sets occurring at ANY finite root in the itinerary are

    {0}, {3}, {1}, {1,2,3}, {0,2}.

Let A be the support at one chronological date. If player i replaces
its ENTIRE clock by any unrestricted behavioral strategy, the opponent
quitters at that date form a subset T⊆A∖{i}. The terminal coalition
is either T, with i continuing, or T∪{i}, with i quitting. Because
absorption occurs at the FIRST date with any quitter, players quitting
at different dates cannot be combined into a later terminal coalition.
This reasoning applies to every finite deadline, Never, mixed clocks
and all full live-history strategies, not only one-period replies.

Prescribed terminal coalitions are the nine nonempty sets

    {0},{1},{2},{3},{0,2},{1,2},{1,3},{2,3},{1,2,3}.

All36 recipient coordinates in those rows are potentially paid and
are retained. The ONLY additional coordinates that an observer's
unilateral reply can create are

    r₀,01, r₀,03, r₀,012, r₀,013, r₀,023, r₀,0123,
    r₁,01, r₁,012, r₃,03, r₃,023.

Hence the following FOURTEEN coordinates are genuinely unused:

| Coalition | Arbitrary recipients |
| --- | --- |
| {0,1} | 2,3 |
| {0,3} | 1,2 |
| {0,1,2} | 2,3 |
| {0,1,3} | 1,2,3 |
| {0,2,3} | 1,2 |
| I | 1,2,3 |

For each listed coordinate (S,i), S is neither a prescribed coalition
nor a subset of A∖{i} nor T∪{i} for any T⊆A∖{i} and any itinerary
support A. The explicit support enumeration gives46 used and14 unused
coordinates, agreeing with the formula. No assumption on their values
is needed. The unreachability claim is recipient-specific: a listed
coordinate (S,i) cannot be paid to i under i's own unilateral replacement.
It need not be unreachable when a different owner deviates; that owner's
cap does not use recipient i's payoff. Changing them independently,
by any finite amount,
leaves each constructed profile's payoff and each owner's ENTIRE
unrestricted cap EXACTLY unchanged. Even a deviator using history to
choose a later phase cannot make two opponent suppliers simultaneous
at a date where their prescribed support does not allow it.

Consequently the finite criterion defines a46-coordinate sufficient
class times an unrestricted14-coordinate affine factor. Fix the polynomial
clearings and their denominator orientations used at the literal table.
Their coefficients depend continuously on the used reward coordinates,
and all original denominator signs, constant comparisons, endpoint signs
and finitely many strict coefficient bounds have positive slack there.
They therefore persist simultaneously on an open chamber in the46 used
coordinates; the other14 may range over ALL real values. This is a finite
uniform sign argument, not pointwise continuity of separate ladder rows.
This is stronger than merely a tiny full60 neighborhood. In particular
grand rewards for recipients1,2,3 may be arbitrary without affecting
the constructed approximate-equilibrium family. A new sure-root or
known producer may incidentally appear after such changes; the direct
constructor remains valid and never uses absence of those alternatives.

## 8. Legal finite periodic profiles and complete behavioral caps

Fix one zero Y* of Ψ before choosing an accuracy, and let
V=(s₀,b,s₂,d). The produced forward continuation-to-head circuit is

    V → V₁ → V₂ → U → W → V.

The first, second and last arrows are limits of the actual full-Nash
ladders proved in Section 5. The middle arrows are the literal solo1
and triple123 roots. Every finite ladder row and both literal roots
are full Nash against their displayed annotations. Charges are
summable on the ladders; all their annotations converge to the
displayed endpoints. Summability alone is not used to assert that
the infinite itinerary is playable on ℕ.

### Finite truncation and order

Truncate each of the three ladders at a finite length, at least one,
and retain both literal roots. Concatenate these five finite lists
in the forward order above. Reverse the ENTIRE concatenated list,
including its piece order, to obtain one actual chronological period.
The roots are prescribed calendar hazards, implemented by independent
private coins whenever play is still live. Repeat that finite period
forever.

This reversal is necessary because F(v,q) places q before its
continuation v. A later application in a forward predecessor list
is an earlier root in actual chronology. No root is inserted after
an infinite ladder at a finite ordinary date, no empty date is
silently added, and no strategy is reset to a limiting port by fiat.

Let E be the sum of the three sup-norm endpoint errors caused by
truncation. Each error tends geometrically to zero, hence E→0.
Define the scalar one-root companion

    Hᵢ(q,z)=max(Qᵢ(q), Rᵢ(q)+hᵢ(q)z).

It is monotone and hᵢ-Lipschitz. Full root Nash at annotation v gives
Hᵢ(q,vᵢ)=Fᵢ(v,q), including quiet or sure coordinates. For the
finite forward list let f be the prescribed affine composition and
Tᵢ the composition of its Hᵢ in the same application order. Write

    C=∏_{roots}c(q),       κᵢ=∏_{roots}hᵢ(q).

Then f is C-Lipschitz and Tᵢ is κᵢ-Lipschitz. These are precisely
the prescribed and best-response block maps in the reversed
chronological word, by finite backward induction.

All root maps have Lipschitz constant at most one. Compare each
finite piece at its reference input with its intended endpoint,
then telescope across the five pieces. The full-Nash identity for
H transports the same reference annotations. Therefore

    ‖f(V)−V‖∞≤E,       |Tᵢ(Vᵢ)−Vᵢ|≤E for every i.       (12)

There is no word-length times E term. In particular this argument
does not claim that every root of the actual truncated periodic
profile remains exactly Nash at its new periodic continuation.

### Joint and deleted-opponent contraction

The first solo0 rate and first solo3 rate of the forward ladders
are fixed, strictly positive numbers once Y* is fixed. Retain them
in every truncation. Consequently there are constants C*<1 and
κᵢ*<1 independent of truncation such that

    C≤C*,       κᵢ≤κᵢ* for every i.

For each i at least one of those two distinct suppliers is an
opponent. Thus deleted-opponent survival, not only prescribed
joint survival, is strictly contractive. All finite-word rates
are less than one, so no boundary conditioning is required.

The repeated word absorbs almost surely. Its actual terminal payoff
U* satisfies U*=f(U*) by conditioning on the first period. This
affine contraction has a unique fixed point, and (12) implies

    ‖U*−V‖∞≤E/(1−C).

Let M=max_{S,i}|rᵢ(S)|. Every actual terminal payoff lies in [−M,M].
The displayed convergence also proves V lies there. For the literal
table in Section 6, V and every reference annotation lie in [−5,5]⁴:
all finite reference root maps are convex combinations of their
annotation and rewards, and all reference endpoints are limits of
such combinations.

### Identification of every full cap, including Never

Censor the repeated game after m whole periods, giving zero if no
absorption has occurred by then. Finite dynamic programming, allowing
all unilateral actions at every remaining date, gives the cap
Tᵢᵐ(0). For EVERY unilateral behavioral strategy, including Never
and deadlines beyond the censoring date, censoring changes expected
terminal payoff by at most Mκᵢᵐ.

Indeed a difference is possible only if every OPPONENT survives all
m periods. Their prescribed survival is κᵢᵐ regardless of the
deviator's private decisions. If the deviator has already quit the
difference is zero; otherwise any eventual reward has absolute value
at most M. This uses neither the deviator's prescribed survival nor
a stationary restriction. Taking suprema preserves this uniform
bound.

It follows that the unrestricted Bᵢ* is the limit of Tᵢᵐ(0),
and hence is the unique fixed point of the scalar contraction Tᵢ.
Apply (12) again:

    |Bᵢ*−Vᵢ|≤E/(1−κᵢ),
    0≤Bᵢ*−Uᵢ*≤E/(1−κᵢ)+E/(1−C).                    (13)

Every mixed clock and full-history behavioral strategy is covered.
Never is not assigned an artificial zero floor: when opponents
absorb, its passive payoff may be negative. The censoring proof
correctly retains that payoff in the limiting cap.

Since E→0 and the contraction collars are uniform, choose truncations
to make (13) and the payoff error arbitrarily small. This proves the
terminal statement of Section 1 at the one fixed target V.

## 9. Boundary tests and why deleted survival is essential

### One supplier is not enough, even at an exact annotated fixed point

For every nonempty coalition S set

    r₀(S)=−1 if 0∈S, otherwise 0;
    rᵢ(S)=−2 if i∈S, otherwise 0, for i=1,2,3.

Never pays zero. Against annotation v=(−1,0,0,0), take
q=(p,0,0,0), with 0<p<1. Owner0 ties, each observer strictly
prefers Continue, and F(v,q)=v. Thus this is a full binary Nash
root with positive joint charge and joint survival 1−p<1.

But h₀=1 and H₀(q,z)=max(−1,z). Repeating q gives owner0 prescribed
payoff −1, while its actual Never deviation pays 0. Its debt is 1.
The formal scalar fixed point −1 is not the true cap. Joint charge
alone cannot identify full responses; two distinct suppliers give
the missing deleted-opponent contraction in Section 8.

### Finite tails and signed rewards

A finite last block followed by Never is not a substitute for the
periodic construction. Its last active root would face continuation
zero instead of the intended matching port. The construction repeats
the entire finite reversed word; that actual periodic continuation
is obtained by the affine fixed point, not assumed.

No own-sign assumption is used in the compiler. With negative rewards,
censored finite caps may approach a negative fixed point. The
uniform Mκᵢᵐ estimate, rather than a supposed nonnegative cap floor,
proves the correct full cap. The preceding one-supplier test shows
exactly why this signed argument needs contraction.

### Noncontractive scalar closure and uniform late-row inequalities

The return equation need not have a unique zero or a contractive
return map. Opposite exact signs of the reward-derived scalar Ψ
and nonvanishing original denominators suffice. Choose one zero
once. The pair spectators may start BELOW their own singletons;
requiring them above would discard the example. The factored
conditions (9) check every row down to the binding limit and supply
the uniform perturbation proof, not just separate finite-row
continuity.

## 10. Source correspondence and original uniform endpoint

The exact root companion identity is already represented by
`quittingRootCompanionMap_eq_max_endpoints` in
`UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`.
Its endpoints are exactly Qᵢ and Rᵢ+hᵢz here.
`quittingCompanionComposite_of_isQuittingCyclicResponseSolution`
and `quittingCyclicResponseSolution_eq_companionLabel_fixedPoint`
in that file describe supplied periodic response solutions and
their scalar fixed points under deleted-period survival <1.
`quittingCompanionComposite_eq_compList_apply` in
`UniformEquilibrium/Quitting/Cycles/CompanionTransport.lean`
identifies finite max-affine composition. These are reused
one-root/composition principles, not new raw reward producers.

`quittingPureTimeValue_periodizedPrefix_block_interpolation` and
`quittingBestReplyValue_periodizedPrefix_le_max` in
`UniformEquilibrium/Quitting/Cycles/PeriodicFiniteReplyPrefix.lean`
give exact later-block values and unrestricted periodic-prefix
reply bounds. Section 8 supplies its own full signed cap argument;
it does not import an assumed response solution, a prescribed
deadline attaining the cap, or an omitted empty-phase convention.

The new producer content is the explicit scalar elimination,
finite coefficient tests and uniform ladder inequalities in
Sections 2–5. The finite truncation seam (12), applied to a closed
chain of convergent Nash ladders rather than an already closed
finite exact cycle, supplies the terminal acceptance family.

For the last semantic step use
`quittingGame_uniformPayoffWitnesses_of_terminalTargetAcceptance_family`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Its input is an indexed family of actual behavior profiles such
that, for every positive error, some family member is terminal
approximate Nash and has terminal payoff within that error of
one fixed target. Section 8 proves exactly this hypothesis.
The theorem keeps a member of that actual family as the witness
and provides a horizon threshold valid for every later horizon,
for both unilateral horizon regret and payoff delivery.

This consumer has no positive-own or normality premise. The
bounded one-date delay between selection and absorbing rewards
matches the game semantics in Section 1. No new conditional
terminal-to-uniform claim or weaker asymptotic target is substituted.

## 11. Bounded whole-selection overlap evidence

The literal table is not offered as a counterexample: Section 8
constructs its approximate equilibria. The following exact tests
show why several applicable existing reward-only producers do
not already supply this example. These comparisons are over
their full named finite selection sets, not one failed choice.
They do not assert a complete census of all possible UE proofs
or exclude an existential safe-child selection not listed here.

### All sure-root and persistent-base selections

At every real continuation annotation the literal table has no
full Nash root with a sure coordinate. The favorite map of its
positive singleton join is

    f(0)=3,       f(1)=2,       f(2)=0,       f(3)=1.

If three or four players are sure, a sure member's withdrawal
gain is 1: its Quit-minus-Continue gap is 4−5=−1 when the last
player continues, or −5−(−4)=−1 when the last player quits.
With exactly two sure, every pair has a member whose participant
pair payoff is strictly below its passive payoff at the other's
singleton. Its gap is negative if neither free player joins and
−1 if one or both join. With exactly one sure z, every free
nonfavorite i≠f(z) has a uniformly negative gap: its pair entry
−2 is below its passive singleton entry, and all larger-coalition
gaps are −1. These two players must be quiet. Favorite f(z) then
has a positive join gap and must be sure, reducing to the excluded
two-sure case. All rate and annotation boundaries are included.

Each true unrestricted punishment value is −4. Never against
arbitrary opponents guarantees at least −4 because every passive
reward is ≥−4. Opponents all quitting immediately bound the
player's best reply by max(−4,−5)=−4. Thus no punishment-priced
sure-root or induced persistent-base selection can repair the
absence of ANY sure-coordinate root by changing its continuation.

### Product premiums, participant protection and payoff-deficit tests

`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
fails on a pure triple: each active forced-Quit reward is 4>1.
`IsSupportwiseQuittingPremiumWeightCertificate` in
`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`
fails for every normalized nonnegative choice of weights on that
support, since every premium is 3.

`HasProtectedParticipantPremiums` and
`HasSupportSpecificQuittingLeavers` in
`UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`
cannot protect any owner: the participant grand reward −5 is
below its own singleton 1. Choosing no protected players leaves
the positive-premium triple trap with no protected leaver.
Participant-only hypotheses fail because passive rewards are nonzero.

A strict deficit below the own-singleton vector for all actual
product laws is false. The literal rates (2/3,0,1/2,1/2), followed
by Never, yield

    U=(3/2,23/12,19/12,11/6),

strictly above 1 in every coordinate. This test is not Nash;
its role is to rule out that quantified payoff-deficit premise.

The per-support upper-average-or-boxed-charge test also fails
on support {0,1,2}. At the full triple its normalized weighted
premium is 3 for every weight choice. The alternative charge
coefficients obey d≤5/2, g≤5/2, τ≥3 and ℓ≤1 from singleton
and penultimate-subset tests. Hence their largest threshold is

    3(d/τ)(g+ℓd/τ)≤25/3<3+3M=18.

This is an all-coefficient exclusion, not a guessed-weight failure.
The charge definitions are `QuittingTrapChargeCoefficients` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`
and `HasBoxedQuittingNashCharges` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`.

### Complete relabeling tests for selected phase families

For `RawRegion` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`,
every partition into two pairs fails the outsider-join condition:
an outsider joining the other whole pair gets participant triple
reward 4>1+1/50. The consumer
`exists_exact_allSuffix_uniformPayoff_of_rawRegion` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleEquilibrium.lean`
therefore has no raw-region choice on this table.

The `RawFamily` used by
`exists_uniformEquilibriumPayoff_of_rawFamily` in
`UniformEquilibrium/Quitting/Cycles/BelowSingletonJointPhaseSource.lean`
requires two equal below-own passive singleton values in each
recipient row. Row0 has other-singleton values 4,0,4 and only
one is below its own value 1. Every relabeling fails.

The strict and weak raw sources `RawSource` and `WeakRawSource`
in
`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`
require two lower/nonpositive singleton levels in the corresponding
row; row0 rules out every ordering. Its inverse alternative
`InverseRawSource` requires participant scheduled-pair rewards
at least own; every pair has a member with reward −2<1, so
every matching fails.

The raw cyclic-child source `RawTable` in
`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`
and `RawRows` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildSingletonAdapter.lean`
requires a pivot singleton column below own for all three other
recipients. No singleton column has that property. This excludes
all pivot/relabel choices of that raw source, not arbitrary
existential quiet-child equilibria.

### Full Γ-family and cycle/core checks

Define Γᵢⱼ=rᵢ,j−sᵢ for i≠j and Γᵢᵢ=0. The literal table gives

    Γ=[ 0, 3,−1, 3;
        2, 0, 1,−3;
        2,−2, 0,−1;
       −1,−2, 1, 0 ].

For the raw triple inverse criterion consumed by
`exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`,
all four triples fail. The 012,013,123 principal inverses have
negative entries, respectively local entries (1,2)=−1/5,
(1,0)=−1 and (2,0)=−1/4. The 023 principal inverse is

    (1/5)[1,3,1; 1,3,6; 2,1,2],

but outsider1's inverse weight is (−3/5,6/5,2/5), so its passive
row premise fails. Every triple choice is covered.

The principal 13 matrix [0,−3;−2,0] has no ordinary nonnegative
complementarity solution at offset (−1,−1), excluding the
corresponding all-principal Q requirement. These failures are
not inferred from a stationary search.

For `SignedFourCycleSingletonData` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`,
all cyclic orderings fail: row1's only negative successor is3,
forcing predecessor1 at row3, but Γ₃₁=−2 contradicts predecessor
positivity. For `IsLiteralStrictFiniteOddIntervalBlockerCore` in
`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCoreRowAdapter.lean`,
each owner's blocker-absent lower bound is ≤own=1 while its
passive upper bound is ≥5 from a passive pair. The required
strict separation fails for every odd-core embedding.

These are bounded source comparisons. The class theorem rests
on its direct construction, not on an assumption that all
previous UE producers have been exhausted.

## 12. Narrow Lean handoff and nonclaims

A raw structure should store the reward table and the finite
strict constant/coefficient tests only. It must not store a
closed word, rates, continuation ports, a Nash-selection field,
or the desired approximate-equilibrium family as assumptions.

The natural proof stages are:

1. Polynomial coefficient domination proves every original
   denominator and interval inequality.
2. The displayed membership-gain elimination derives all triple
   active equalities and scalar elimination derives the two
   intermediate matching constraints.
3. IVT gives one zero of Ψ; all five ports and rates are defined
   from that zero.
4. The factored solo/pair inequalities prove full Nash for every
   finite ladder row and establish convergent endpoints.
5. A finite-list seam theorem proves (12), retaining whole-word
   reversal and fixed distinct supplier roots.
6. Scalar companion contraction and uniform censoring give (13)
   for every behavioral deviation.
7. Apply the existing fixed-target acceptance-family consumer.
8. A recipient-specific support mask proves invariance under
   all fourteen coordinate changes and the full open chamber.

Likely new theorem shapes are a reward-only scalar-circuit
producer, a finite closed-ladder truncation compiler, a raw
criterion-to-uniform-payoff consumer, and payoff/cap invariance
under agreement on the 46 response coordinates. These are
ordinary mathematical targets here, not asserted new Lean
declarations. Existing companion and uniformization machinery
should be reused under its exact hypotheses.

The result does not claim exact Nash for any one finite period,
an absorbing approximate equilibrium for every arbitrary table,
finite-support completeness, execution of ω+ω phases, preservation
of one prescribed circuit under arbitrary perturbation, or
global completion of the four-player conjecture. The sufficient
class is the finite reward criterion actually proved above.
