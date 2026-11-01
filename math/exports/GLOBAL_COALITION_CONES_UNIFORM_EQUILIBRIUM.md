# Global coalition cones produce uniform equilibria

Ordinary mathematics; no new Lean certification is claimed.

## 1. Raw hypotheses

There are n>=2 players. Native quitting rewards are finite real vectors Z(D),
for nonempty coalitions D. Live play, literal Never, and own singletons are
zero: Z_i({i})=0. At each natural date owners independently choose Continue
or Quit; the first nonempty coalition absorbs. Before absorption there is
one live history per date, so behavioral strategies are independent laws
on finite first-Quit dates and a separate Never point. Every unilateral
behavioral replacement is allowed; no public randomizer is used.

Let Gamma[:,j]=Z({j}), and put J_ij=Z_i({i,j}) for i!=j with zero
diagonal. Suppose Gamma is invertible with
M=Gamma^{-1} strictly positive entrywise. Put

    lambda = 1^T M,
    rho = min_{i,j} M_ij/lambda_j > 0.

Thus every nonzero v>=0 satisfies (Mv)_i >= rho sum(Mv).
Necessarily rho<=1/n. Define the raw coefficient vectors

    a^D = M Z(D).

For every nonempty coalition D define its joining-loss vector by

    ell_i^D = 0                         if i in D,
              Z_i(D)-Z_i(D union {i})   if i outside D,
    b^D = M ell^D.

(The grand coalition has ell=b=0.) Suppose there are constants

    kappa >= 0,           L=1+(n-1)kappa,
    0 <= eta < e < rho,    tau > 0,
    eta + (L-eta)/(1+(rho-e)/tau) <= e,

such that, for every nonempty D,

    sum(a^D) >= 0,
    a_i^D >= -kappa sum(a^D)            for every i,
    a_j^D <= eta sum(a^D)               whenever j outside D,
    sum(b^D) >= 0,
    |b_i^D| <= tau sum(a^D)             for every i.

All these are finitely many raw inequalities. Singletons satisfy a^{j}=e_j
automatically. No invertibility or sign assumption on Gamma-J is needed.
A convenient strict-margin choice is

    kappa=1, L=n, e=rho/2, eta<=rho/8, tau<=rho^2/(16n).

The nonnegative-coefficient case is recovered by kappa=0, L=1; then
tau<=rho^2/16 is a convenient sufficient bound.

The exact scalar feasibility threshold, allowing e to be optimized, is

    tau <= (sqrt(L-eta)-sqrt(L-rho))^2,

with e=L-sqrt((L-eta)(L-rho)); strict inequality allows a strict collar.
Indeed the equivalent inequality is

    tau <= (e-eta)(rho-e)/(L-e).

Its maximum over eta<e<rho is the displayed square-root expression.
For the simple kappa=1 choice, g=1+(rho-e)/tau>=1+8n/rho, and
eta+(n-eta)/g<rho/4, leaving a strict output margin below e=rho/2.

**Theorem.** The infimum of full Nash debt over absorbing native quitting
profiles is zero. Here full debt is the sum of each owner's complete
response supremum minus its prescribed terminal payoff. The conclusion
transfers to an original quitting table with
nonnegative own-singleton values s_i after normalizing
Z_i(D)=r_i(D)-s_i for every nonempty D, provided the normalized table satisfies
these hypotheses. Thus one payoff target exists such that every positive
accuracy admits a behavioral profile satisfying the payoff and deviation
bounds at every sufficiently long horizon; the target is fixed before
the accuracy.

This closes BOTH the positive-global-minimum and AllNever alternatives on
the displayed raw region. It constructs the profiles from finite game data;
no recurrence, selected continuation, strategic witness or exact realization
of a minimizing carrier point is assumed. Section7 gives an open Fin4
region outside the stationary and sure-first punishment mechanisms.
Arbitrary Fin4 rewards remain outside the theorem's scope.

## 2. Exact root identities at arbitrary hazard size

Let q in [0,1]^n be a Nash equilibrium of the one-stage stop/continue game
with continuation payoff w. Write

    h = product_i (1-q_i),
    p_D = product_{i in D} q_i product_{i outside D} (1-q_i),
    R = sum_{D nonempty} p_D Z(D),
    U' = R + h w.

Let Q_i be player i's payoff when she certainly quits at this root against
q_{-i}. The Nash inequalities imply

    s=U'-Q >=0,                q_i s_i=0.

Indeed U'_i is the maximum of her quit and continue offers; equality with
the quit offer holds whenever q_i>0, including q_i=1. This includes all
boundary roots and needs no full mixing.

Own-singleton zero gives the exact identity

    R-Q = sum_{D nonempty} p_D ell^D.

To check coordinate i, let pi_i(E) be the independent probability that
exactly the opponents in E quit. The contribution is
(1-q_i)pi_i(E)[Z_i(E)-Z_i(E union {i})]. For E empty this is
zero, because both live reward and own singleton are zero. For E nonempty
it is precisely p_E ell_i^E. Define

    x=Mw,                 A=sum_D p_D a^D,
    B=sum_D p_D b^D,      x'=MU',       z=Ms.

Then, exactly,

    x'=h x+A,             z=h x+B.

The raw inequalities imply

    sum A>=0, A_i>=-kappa sum A,
    sum B>=0, |B_i|<=tau sum A.

If q_j=0, every positive-probability coalition omits j, so

    A_j<=eta sum A.

## 3. The global collar and survival ratio

Assume a=sum x>0, x_i>=-kappa a for every i, and min_i x_i<=e a.
If h=0, the root is already absorbing and no further geometric claim is
needed. Suppose h>0.

Since s>=0, z=Ms is in the positive image cone. Moreover

    sum z = h a+sum B >= h a>0,

so every coordinate z_i>=rho h a. Choose i with x_i<=e a. Then

    B_i=z_i-h x_i >= (rho-e)h a,
    sum A >= ((rho-e)/tau)h a.

Put g=1+(rho-e)/tau>1. Thus

    a'=sum x'=h a+sum A >= g h a.

Since s is nonzero, some s_j>0. Complementarity forces q_j=0.
Since every other coordinate is at least -kappa a,
x_j<=a+(n-1)kappa a=L a. Consequently

    x'_j = h x_j+A_j <= L h a+eta sum A,
    min_i x'_i/a' <= eta+(L-eta)/g <= e.

The lower face is also preserved exactly:

    x'_i=h x_i+A_i >= -kappa(h a+sum A)=-kappa a'.

Therefore the same nonzero global collar is invariant under
EVERY Nash root with positive survival. No local chart, degree, selected
root, recurrent word, or infinitesimal approximation is involved.

If nu is the survival probability through the continuation's finite chain,
the prefixed chain has nu'=h nu, and

    a'/nu' >= g a/nu.

This ratio grows uniformly even when the prefix itself absorbs with very
high probability; there is no need for a lower bound on h.

## 4. Start from a virtual terminal payoff and iterate finite games

Fix a player j and epsilon>0. Consider a finite-horizon auxiliary game with
forced terminal payoff

    w_0=epsilon Gamma e_j.

At horizon zero this is a constant game and hence has zero Nash debt.
Its inverse coordinate is x_0=epsilon e_j, so a_0=epsilon and it lies in
the collar. Prepend a one-stage Nash equilibrium against its current
continuation payoff. Such a root always exists by finite-game Nash
existence. Inductively this creates a finite game equilibrium: after any
root continuation, each player faces the previously constructed equilibrium,
and the root quit/continue inequalities verify every strategy by backward
induction. Only the surviving history needs a continuation.

If any prefixed root has h=0, the prescribed finite game profile already
absorbs. Otherwise repeat indefinitely in this purely finite construction.
Writing nu_k for survival to the forced terminal payoff and a_k=sum M U_k,
Section 3 gives

    a_k/nu_k >= g^k epsilon.

Every U_k is a convex combination of the finitely many native rewards and
w_0, so a_k is bounded above by a constant C_epsilon independent of k.
For example C_epsilon=||lambda||_1 max(max_D||Z(D)||_infty,
||w_0||_infty) works, since a_k=lambda U_k>=0. Therefore

    nu_k <= C_epsilon/(epsilon g^k) -> 0.

No compactness passage to an infinite chain is needed.

## 5. Remove the virtual terminal payoff and absorb literal Never

Realize a finite equilibrium chain by the same independent behavioral
hazards in the native infinite quitting game, and continue forever after
its finite horizon. Its literal joint Never probability is nu_k.

For prescribed play, replacing the forced terminal payoff w_0 by zero
changes each payoff by at most ||w_0||_infty. For any unilateral infinite
deviation, collapse all choices after the finite horizon to reaching the
virtual terminal. Conditional on reaching that horizon, all opponents then
continue forever. In the actual game the deviator can either quit alone
or Never; both give native payoff zero. In the finite auxiliary game the
payoff is w_{0,i}. Earlier terminal outcomes agree. Hence every deviation
payoff differs from its collapsed finite-game payoff by at most
||w_0||_infty. Exact finite-game Nash therefore implies full native debt
at most 2||w_0||_infty per player, uniformly in k, including the literal
Never reply and arbitrary randomized infinite deviations.

If a root had h=0, the prescribed profile is already absorbing and this
alone proves debt sum <=2n||w_0||_infty.

Otherwise choose a player whose individual Never atom is at most
nu_k^{1/n}. Move that player's Never atom to a fixed finite time after the
chain. The prescribed profile now absorbs surely. The standard one-atom
perturbation estimate bounds the change in full debt sum by

    2 R (2n-1) nu_k^{1/n},

where R=max_D ||Z(D)||_infty (enlarging R harmlessly). This follows by
coupling: prescribed payoffs change by at most 2R times the moved mass;
for every other player's unilateral reply, the opponent law changes on
at most that mass; for the modified player's cap, opponents are unchanged.
The estimate is uniform over all finite and Never replies.

Consequently, for every epsilon>0 the infimum absorbing debt is bounded by
2n epsilon ||Gamma e_j||_infty, after letting k increase. Let epsilon tend
to zero. The infimum absorbing native debt is exactly zero.

## 6. Original-game transfer

Suppose original own-singleton values s_i are nonnegative and all other
native rewards are obtained by subtracting s_i from each nonempty original
terminal reward. On an absorbing prescribed profile, native and original
prescribed payoffs differ by exactly s_i.

Every fixed finite stopping-time reply terminates surely, and its original
payoff is its native payoff plus s_i. For native own-singleton zero, the
best-response cap over finite replies equals the cap over all replies:
late finite deadlines approximate literal Never by bounded convergence.
For the original game, s_i>=0 ensures that late finite deadlines have
limit at least the literal Never payoff. Hence its full cap also equals
its finite-reply cap. Thus original and native full debt agree on every
absorbing prescribed profile.

The constructed absorbing all-errors Nash profiles therefore apply to the
original game. The existing terminal-all-errors consumer yields an
ordinary uniform-equilibrium payoff; this final semantic consumer is an
existing Lean result, while the coalition-cone producer above remains
ordinary mathematics.

## 7. An exact Fin4 game requiring a different global construction

The original game in this example is r_i(D)=Z_i(D)+1 for every nonempty
D, with original live/Never reward zero. The following defines its native
table completely. All comparisons are against unrestricted deviations.

### The raw data

Put

    Γ=[0,-2,-5,4; -6,0,-4,6; 1,3,0,-5; 1,-1,4,0],
    β=10^-6, α=1-β, δ=10^-24, M=Γ^-1.

Exactly,

    M=[26/21,17/42,31/21,41/21;
       38/21,41/42,55/21,68/21;
       1/7,1/7,2/7,4/7;
       4/3,2/3,5/3,7/3],
    λ=1^T M=(95,46,127,170)/21, ρ=3/95, det Γ=42.

For singletons let a^{j}=e_j. For every pair D let a^D=α1_D. Set

    a^012=α1_012-2δe0,
    a^013=α1_013+δe0,
    a^023=α1_023-4δe0,
    a^123=α1_123-δ(0,64,29,28),
    a^I=α1-3δM1.

Define ALL rewards by Z(D)=Γa^D. Every a^D is supported on D and strictly
positive on D. Hence own singletons are zero. Relative to the common-α
completion, the only reward perturbations are δ times

    R012=(0,12,-2,-2), R013=(0,-6,1,1),
    R023=(0,24,-4,-4), R123=(161,-52,-52,-52), RI=-3·1.

All rewards have absolute value <20 (and hence <100). Let
ell_i^D=Z_i(D)-Z_i(D+i) for i outside D, zero for i inside D; b^D=M ell^D.
For singleton j, ell^{j}=βΓe_j and b^{j}=βe_j. For pairs the nonzero
outsider loss coordinates, divided by δ, are

| D | Outsider losses ell/δ |
|---|---|
|01|ell2=2, ell3=-1|
|02|ell1=-12, ell3=4|
|03|ell1=6, ell2=4|
|12|ell0=0, ell3=52|
|13|ell0=0, ell2=52|
|23|ell0=0, ell1=52|

For the triple omitting i, ell_i/δ is respectively 164,27,4,1 for i=0,1,2,3.
Grand-coalition loss is zero. Thus 1^T b^D is STRICTLY positive for every
nonempty proper D. For the two signed pair rows, its numerators over 21 are
84 and128, respectively; all other rows are visibly positive.

Use κ=1, L=4, η=ρ/8, e=ρ/2=3/190, τ=ρ²/64=9/577600.
The singleton ratio is β<τ.
For nonsingleton D, sum a^D>1 and max_i |b_i^D|<=656δ<τ: every entry of M
is <4 and sum_i |ell_i^D|<=164δ. (The grand loss is zero.) Hence every
raw signed-cone hypothesis holds strictly, except the structural zero
joining loss at the grand coalition. In particular, zero coefficient
coordinates are strictly above -κ sum a^D and strictly below the positive
outside upper bound. The collar scalar inequality is strict by Section1.

### Complete stationary comparisons

For a stationary hazard q, let

    H_i=prod_{j!=i}(1-q_j),
    Q_i=E Z_i(B+i), P_i=E[Z_i(B)1_{B nonempty}],
    F_i=(1-H_i)Q_i-P_i.

At any nonzero stationary q the Bellman Nash signs are F_i=0 for 0<q_i<1,
F_i<=0 for q_i=0, F_i>=0 for q_i=1. This includes literal Never and all
complete finite replies by the stationary Bellman identities. We prove there
is no such q except q=0, which is the nonabsorbing AllNever Nash profile.

For all proper coordinates define x_i=q_i/(1-q_i) and
v_i=αq_i+βx_i. The map q_i↦v_i is strictly increasing, with v_i>0 iff q_i>0.
The common-α table has exactly

    F_i/H_i=-(Γv)_i.

The perturbations will be retained exactly below, not dropped as small
collision probabilities.

#### Proper supports of size at most three

A singleton support j is impossible: every column Γ[:,j] has a negative
entry, and that quiet owner's stationary gap is
Γ_ij q_j(αq_j-1)>0. On a two-owner proper support, either active equation
requires Γ_ij v_j=0, impossible.

For support S of size three, put A_jk=x_jx_k-q_jq_k. This is strictly
positive and strictly increasing in each positive coordinate x_j,x_k.
The three active equations are exactly

    (Γ_SS v)_i=δR_i(S)A_jk, {j,k}=S minus{i}.

For S012 the i=0 equation reads -2v1-5v2=0, impossible. For S023 the
i=3 equation reads v0+4v2=-4δA02<0, impossible. For S123, Γ_SS^-1 is
strictly positive whereas all three right sides are negative, forcing v<0.
For S013, the equations are

    v1=2v3,  v0-v3=δA03,  v0-v1=δA01.

Since v1>v3, x1>x3, so A01>A03. But subtraction gives
v3=δ(A03-A01)>0, contradiction. This covers every proper support, independent
of quiet-owner comparisons.

#### Proper full support

Let p_D be the stationary root's independent coalition probabilities, h the
all-Continue probability, A=sum_{D nonempty}p_D a^D and B=sum p_D b^D.
The actual stationary payoff U satisfies x=M U=A/(1-h)>=0 with sum x>0.
Every active owner is indifferent, so U=Q. The elementary root identity
M(U-Q)=h x+B therefore gives

    0=h sum x+sum B>0,

since h>0 and every sum b^D>=0. This excludes full proper support directly
from the verified raw cone inequalities, without an asymptotic estimate.

#### Even arbitrarily accurate stationary Nash is impossible

If a sequence of absorbing stationary profiles had full debts tending to
zero, compactness gives a hazard limit q. If q!=0, stationary prescribed
values are continuous because joint one-step absorption stays positive.
Immediate Quit and waiting one step then using the prescribed continuation
are two legal complete deviations. Their limiting inequalities make q Nash
against its own stationary value, contradicting the complete census.

If q tends to zero, normalize q by its total hazard and extract r>=0,
sum r=1. Stationary payoff converges to Γr, whereas immediate Quit tends to
zero, so Γr>=0. For 0<r_i<1, the literal Never payoff converges to
(Γr)_i/(1-r_i), hence zero limiting debt gives r_i(Γr)_i=0. The same
complementarity holds trivially at r_i=0 and at r_i=1, the latter because
Γ_ii=0. But Γ^-1>>0 makes Γ an R0 matrix: if y=Γr>=0 is nonzero then
r=My>>0, and complementarity forces y=0; if y=0, invertibility gives r=0.
Both contradict sum r=1. Thus the stationary full-debt infimum is strictly
positive. This rules out stationary approximate producers as well as exact
stationary ones.

For the explicit original table r_i(D)=Z_i(D)+1 on every nonempty D,
this also excludes all stationary uniform-equilibrium producers. At any
nonzero stationary profile, joint absorption is certain. If at least two
owners have positive hazards, every opponent-deleted family absorbs, so
adding1 shifts every prescribed and complete-deviation payoff by1 and
preserves all debts. With only one active owner, that owner's native debt
and raised debt are both zero; every quiet owner's debt is unchanged by
the same opponent-absorption argument. Thus every nonzero stationary
profile has exactly the native debt. At AllNever each of four players gains1
by quitting, so original total debt is4. The original stationary debt
infimum is therefore strictly positive. Taking large horizons of any fixed
stationary profile shows it cannot supply arbitrarily accurate uniform Nash.

### No sure-quitter root at any actual continuation

This stronger statement proves separation from the full sure-first
punishment-tail producer, not merely from stationary profiles. Let w be ANY
vector in [-100,100]^4, and let q be a one-stage Nash root against w. The
comparison is g_i=Q_i-P_i-H_iw_i. Suppose some q_i=1.

#### Full active support

The exact weighted joining-loss identity is

    sum_i λ_i(1-q_i)g_i=-h λw-sum_{D nonempty proper}p_D λell^D.

Here h=0. If every owner is active, every nonsure owner is indifferent and
all sure terms have factor zero, so the left side is zero. Strict positivity
of λell^D on EVERY nonempty proper D rules out any nonsure coordinate:
its omission with all other owners quitting has positive product probability.
If all four owners are sure, at least one, in fact every, owner prefers
withdrawal, because the loss on its opposing triple is strictly positive.

#### At most two active owners

A singleton sure root is blocked by an outsider with Γ_ij<0, whose joining
gap is -βΓ_ij>0. If one owner is sure and the other is mixed, the latter's
gap is -βΓ_ij!=0. If both are sure, every pair except01 has a member with
Γ_ij>0 and therefore a negative joining gap. At pair01, player3 has joining
gap δ>0. Hence there is no root with at most two active owners.

#### Three active owners

If all three are sure, a participant has R_i(S)<0 for every triple S:
choose i=2,1,2,1 on S=012,013,023,123, respectively.

If two owners are sure and the third j is mixed, j's gap is δR_j(S), so
j must be0 and S is012,013 or023. Writing z=q0∈(0,1), a sure owner's gap
is respectively

    S012, owner2: -3β(1-z)-2δz<0;
    S013, owner1: -6β(1-z)-6δz<0;
    S023, owner3: -4β(1-z)-4δz<0.

If only i is sure and the other two j,k are mixed, their equations are

    -βΓ_ji(1-q_k)+δR_j(S)q_k=0,
    -βΓ_ki(1-q_j)+δR_k(S)q_j=0.

An interior solution requires Γ_ji and R_j(S) to have the same nonzero
sign, and likewise for k. The finite sign census leaves only

    S013, i=0, q1=q3=t=β/(β+δ).

At that candidate, owner0's necessary sure-Quit inequality is exactly

    w0 <= (Q0-P0)/H0 = -2βt/(1-t)=-2β²/δ=-2·10^12.

This contradicts w0>=-100. Thus NO sure-quitter Nash root exists at any
continuation in the entire reward box. Every actual continuation payoff or
full cap, and any punishment value obtained as an infimum of such values,
lies in that box. Hence every sure-first punishment-tail certificate is
excluded, independently of which tail or punishment selector is used.

For the original table r=Z+1, a root against continuation u has precisely
the native comparisons against u-1. Every actual original continuation
payoff or full cap gives u-1 inside the same box. Thus this exclusion also
covers the original sure-first punishment construction.

### Further coverage comparisons, with exact scope

The witness fails the singleton no-mutually-negative-pair screen at01.
Its determinant is positive and its inverse is strictly positive, so the
negative-degree and missing-positive-inverse-column exits do not apply.

All three alternating-pair partitions fail any criterion requiring every
scheduled c_i=J_i,m(i)-Γ_i,m(i)>0: c_i=-βΓ_i,m(i), and Γ has no partition
into two mutually negative pairs. Criteria requiring simultaneously
p_i>=0 and c_i>0 fail even at one scheduled coordinate, since p_i=αΓ_i,m(i).
The all-support stationary and sure-first arguments above are stronger than
screening any specified stationary or punishment parametrization.

For scalar/support-filtered H/J ledgers, singleton H>=0 means w^TΓ>=0.
Since M is strictly positive, any nonzero such nonnegative weight has FULL
support. The proper product-low condition fails on pair03, where both
participant rewards are positive. The same-sign-pair ledger extension still
fails its proper-triple product-low condition: at support123 choose
q=(0,8/13,29/104,7/26). Then Γq=(unrestricted,1/2,1/2,1/2), and each active
Q_i=α/2+δR_i(123)q_jq_k>0.

Both active Quit offers on pair03 are positive. A proposed nonnegative
weight supported on this pair that gives a nonnegative weighted inserted
payoff at every product root must in particular pass every singleton root.
The inserted payoff vector there is an αΓ column. Hence w^TΓ>=0 forces
full support, contradicting support03. This rejects the weighted trap-leaver
condition over its complete weight selection set.

A larger-trap criterion requiring negative total outside participant
premiums at every singleton of the trap also fails: 123 is a trap, since
each member has a positive participant pair reward within it, but at
singleton1 the sum over recipients2,3 is J21+J31=2α>0.

The only principal triple with nonnegative inverse is123; its inverse is
strictly positive, but the passive outside-row test fails because

    Γ_{0,123} Γ_{123,123}^-1=(-17/52,-31/26,-41/26)<0.

The ordered nonpositive-anchor-block criterion requires Z_c({j})<=0
for marked c in C and j outside C, and a nonpositive weighted participant
total on the first block meeting each quitting coalition. The first test
forces any nonempty marked set C to be closed under the positive Γ arcs. Those arcs are strongly connected, so C=I. The same
pair tests force the first nonempty block to be closed under the positive
arcs, hence it is I; its positive weighted participant sum on pair03 then
contradicts the required nonpositive bound.

These are complete exclusions of the stated mechanisms and selection sets.
They do not classify all nonstationary strategy architectures. The global
producer in Sections1–6 supplies uniform equilibrium on this game and the
raw region, independently of those comparisons.


### Reproducible exact arithmetic

This complete Python/SymPy checker uses rational arithmetic. The exhaustive
mathematical support arguments above supply completeness.

```python
from itertools import combinations
import sympy as s
I=range(4); G=s.Matrix([[0,-2,-5,4],[-6,0,-4,6],[1,3,0,-5],[1,-1,4,0]])
M=G.inv(); lam=(s.ones(4,1).T*M); beta=s.Rational(1,10**6); alpha=1-beta; delta=s.Rational(1,10**24)
rho=min(M[i,j]/lam[j] for i in I for j in I); tau=rho**2/64; e=rho/2; eta=rho/8
assert G.det()==42 and all(t>0 for t in M) and rho==s.Rational(3,95)
assert lam==s.Matrix([[95,46,127,170]])/21
sets=[frozenset(S) for k in range(1,5) for S in combinations(I,k)]
indicator=lambda S:s.Matrix([int(i in S) for i in I])
a={S:(indicator(S) if len(S)==1 else alpha*indicator(S)) for S in sets}
a[frozenset([0,1,2])]-=delta*s.Matrix([2,0,0,0]); a[frozenset([0,1,3])]+=delta*s.Matrix([1,0,0,0]);a[frozenset([0,2,3])]-=delta*s.Matrix([4,0,0,0]);a[frozenset([1,2,3])]-=delta*s.Matrix([0,64,29,28]);a[frozenset(I)]-=3*delta*M*s.ones(4,1)
Z={S:G*a[S] for S in sets}; Z[frozenset()]=s.zeros(4,1)
ell={S:s.Matrix([0 if i in S else Z[S][i]-Z[S|{i}][i] for i in I]) for S in sets}
b={S:M*ell[S] for S in sets}
for S in sets:
 assert all(a[S][i]>0 if i in S else a[S][i]==0 for i in I)
 assert sum(b[S])>0 if len(S)<4 else sum(b[S])==0
 assert all(abs(v)<tau*sum(a[S]) for v in b[S])
 assert all(v>-sum(a[S]) for v in a[S])
 assert all(a[S][i]<eta*sum(a[S]) for i in I if i not in S)
 assert max(map(abs,Z[S]))<20
assert eta+(4-eta)/(1+(rho-e)/tau)<e
R={S:s.zeros(4,1) if len(S)<=2 else s.simplify((Z[S]-alpha*G*indicator(S))/delta) for S in sets}
Rexpected={(0,1,2):(0,12,-2,-2),(0,1,3):(0,-6,1,1),(0,2,3):(0,24,-4,-4),(1,2,3):(161,-52,-52,-52),(0,1,2,3):(-3,-3,-3,-3)}
for S,v in Rexpected.items():assert R[frozenset(S)]==s.Matrix(v)
expected={(0,1):{2:2,3:-1},(0,2):{1:-12,3:4},(0,3):{1:6,2:4},(1,2):{0:0,3:52},(1,3):{0:0,2:52},(2,3):{0:0,1:52}}
for S,v in expected.items():
 for i,c in v.items():assert ell[frozenset(S)][i]==delta*c
for i,c in enumerate([164,27,4,1]):assert ell[frozenset(set(I)-{i})][i]==delta*c
print('PASS: all 60 rewards, supported coefficients, strict proper losses, cone margins, reward box')
# Every pure coalition fails, independently of continuation unless singleton.
for S in sets:
 if len(S)==1:
  j=next(iter(S));assert any(G[i,j]<0 for i in I if i!=j)
 else:
  bad=[i for i in I if (i in S and Z[S][i]<Z[S-{i}][i]) or (i not in S and Z[S|{i}][i]>Z[S][i])]
  assert bad,(S,bad)
print('PASS: every pure absorbing coalition fails')
# Exactly one sure owner and two mixed owners in a proper triple.
candidates=[]
for S in [S for S in sets if len(S)==3]:
 for i in S:
  jk=sorted(S-{i})
  if all(G[j,i]*R[S][j]>0 for j in jk):
   qs={jk[1]:s.cancel(beta*G[jk[0],i]/(beta*G[jk[0],i]+delta*R[S][jk[0]])),jk[0]:s.cancel(beta*G[jk[1],i]/(beta*G[jk[1],i]+delta*R[S][jk[1]]))}
   assert all(0<v<1 for v in qs.values());candidates.append((S,i,qs))
assert len(candidates)==1 and candidates[0][0]==frozenset([0,1,3]) and candidates[0][1]==0
t=beta/(beta+delta);assert all(v==t for v in candidates[0][2].values())
assert -2*beta*t/(1-t)==-2*10**12 and -2*beta**2/delta < -100
# Exactly two sure owners: sole mixed owner must be zero on R.
zeros=[(S,j) for S in sets if len(S)==3 for j in S if R[S][j]==0]
assert zeros==[(frozenset([0,1,2]),0),(frozenset([0,1,3]),0),(frozenset([0,2,3]),0)]
for S,j in zeros:
 sure=S-{j}
 assert any(G[i,next(iter(sure-{i}))]>0 and R[S][i]<0 for i in sure)
print('PASS: exhaustive proper sure-support census and unique candidate threshold')
# Proper triple equations: all requested exact signs.
G123=G.extract([1,2,3],[1,2,3]);assert G123.det()==52 and all(v>0 for v in G123.inv())
assert G.extract([0],[1,2,3])*G123.inv()==s.Matrix([[-s.Rational(17,52),-s.Rational(31,26),-s.Rational(41,26)]])
for S in combinations(I,3):
 if S!=(1,2,3):assert any(v<0 for v in G.extract(S,S).inv())
q=s.Matrix([0,s.Rational(8,13),s.Rational(29,104),s.Rational(7,26)])
assert list((G*q)[1:])==[s.Rational(1,2)]*3
for i in [1,2,3]:
 others=[j for j in [1,2,3] if j!=i]
 assert alpha*s.Rational(1,2)+delta*R[frozenset([1,2,3])][i]*s.prod(q[j] for j in others)>0
assert all(any(G[i,j]<0 for i in I if i!=j) for j in I)
assert alpha*(G[2,1]+G[3,1])==2*alpha>0
# Positive directed arcs strongly connected (either direction convention).
for start in I:
 seen={start}
 for _ in I:seen|={j for i in seen for j in I if G[i,j]>0}
 assert seen==set(I)
print('PASS: triple inverses, higher-support product-low obstruction, positive-arc strong connectivity')
print('PASS: all finite exact checks; completeness is proved by the stationary and sure-root census above.')
```

## 8. Open coverage and formalization handoff

The example has strict signed-cone, outside-coordinate and small-loss
inequalities, and strictly positive total transformed loss on every proper
nonempty coalition. The grand-coalition equality b^I=0 and singleton
identities a^{j}=e_j are structural. Inverse positivity and all other
quantities vary continuously with the native rewards. Therefore the theorem
applies throughout an open neighborhood in every free native reward entry.
The original own rewards are all1, so nonnegative own levels also persist
under small independent perturbations of the original reward table.

The coverage separation is open as well. If two original reward tables
differ by at most epsilon in each entry, every prescribed payoff and every
complete response value differ by at most epsilon, uniformly over all
profiles. Thus full caps differ by at most epsilon and summed debts by at
most2n epsilon. The strict stationary debt gap survives small reward
perturbations. The sure-root cube times the continuation box is compact;
continuity would turn any sequence of nearby sure roots into a forbidden
root at the central table. A small neighborhood keeps every actual
continuation and cap inside the box. Hence this is an open UE region beyond
both complete mechanisms, not just an isolated exact-profile refinement.

The finite root existence input is `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`. The exact full-cap
prefix recursion is `quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
The finite-deadline limit used in the row translation is
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.
The all-errors semantic consumer is
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Its conclusion is one fixed uniform-equilibrium payoff, not a target that
changes with the requested accuracy.

The missing implementation is the signed coalition cone, its exact
joining-loss identity, arbitrary-root collar invariance, and geometric
growth of the continuation-size/ordinary-survival ratio. The finite virtual
terminal construction then gives actual absorbing all-errors Nash profiles
using the explicit complete-response transport and one-atom repair above.
Neither a recurrent orbit nor an equilibrium profile should be assumed as
a structure field: the proof produces both the finite words and their
actual behavioral realizations. The displayed finite arithmetic can be
formalized separately from the general producer. No new Lean proof or
build is asserted here, and the theorem does not settle arbitrary Fin4.
