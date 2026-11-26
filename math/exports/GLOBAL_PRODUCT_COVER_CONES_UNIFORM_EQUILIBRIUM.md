# Global product-cover cones with unrestricted lower grand rewards

Ordinary mathematics for finite quitting games. The new producer is not
Lean-checked. Its output is an actual absorbing approximate equilibrium
against every unilateral behavioral deviation, and hence one fixed uniform
equilibrium payoff under the original-table normalization stated below.

## 1. Exact statement and raw-data adapter

The player set is I={0,...,n-1}, with n>=2. A native quitting table Z has finite terminal rewards,
zero live and literal Never rewards, and Z_i({i})=0. Randomization is private
and independent; deviations may replace an entire behavioral strategy.
At each date all players simultaneously choose Continue or Quit. The first
nonempty quitting coalition determines the absorbing reward; otherwise live
payoffs are zero. Until absorption there is one public history at each date,
so independent laws of stopping dates in the natural numbers plus Never
implement the prescribed profiles. No public correlating signal is used.

For a profile sigma let U_i(sigma) be its expected terminal reward, with
zero on nonabsorption, and let C_i(sigma) be the supremum over all unilateral
behavioral replacements. Full Nash debt means sum_i(C_i-U_i), a nonnegative
quantity. Absorbing means prescribed absorption has probability one.

Choose a finite reference vector V>=Z(I) coordinatewise. Let Zhat agree with
Z on every nonempty proper coalition and let Zhat(I)=V. All conditions below
are on this reference table. Thus the actual grand reward may be arbitrarily
far below its reference value.

Choose an invertible matrix P strictly positive entrywise. This is finite
algebraic certificate data; it is not a strategic object. It need not be the
inverse of the singleton matrix. Put

    rho=min_{i,j} P_ij/(sum_k P_kj)>0.

For every nonempty proper coalition D define

    a^D=P Zhat(D),
    ell_i^D=0                            if i in D,
             Zhat_i(D)-Zhat_i(D union{i}) if i outside D,
    b^D=P ell^D.

For completeness ell^I=b^I=0. No condition on P Zhat(I) is imposed.
Choose kappa>=0 and set L=1+(n-1)kappa. Choose a finite nonempty family
C of positive vectors c. For each c define

    m(c)=min_i c_i-kappa sum_i(c_i-min_j c_j),
    C(c)=max_i c_i.

Require m(c)>0 and choose

    0<rho_star<=rho min_{c in C} m(c)/C(c).

Assume constants 0<=eta<e<rho_star and tau>0 satisfy

    eta+(L-eta)/(1+(rho_star-e)/tau)<=e.

For every nonempty proper D require

    sum a^D>=0,
    a_i^D>=-kappa sum a^D                  for every i,
    a_j^D<=eta sum a^D                     whenever j outside D,
    b_i^D<=tau sum a^D                     for every i.

Replace coefficientwise joining-loss signs by the following raw PRODUCT COVER:
for every q in [0,1]^n, some c in C satisfies

    c dot B(q)>=0,
    B(q)=sum_{empty!=D proper} p_D(q) b^D,
    p_D(q)=product_{i in D}q_i product_{i outside D}(1-q_i).

This is a quantified polynomial condition on finite raw data, not a supplied
root or continuation. Equivalently it can be checked at positive odds z by
requiring some c to satisfy sum_D z_D c dot b^D>=0. Finite C and continuity
extend the latter condition to the closed product cube. Section 8 gives an
explicit finite-coefficient certificate for a genuinely adaptive cover.

**Conclusion.** The infimum of full native Nash debt over absorbing independent
profiles is zero. The constructed prescribed laws never realize the grand
coalition. The conclusion holds simultaneously for every coordinatewise
lowering of the reference grand reward. For original rewards r_i(D)=Z_i(D)+s_i
with s_i>=0, the same absorbing debt conclusion transfers, hence there is an
ordinary uniform-equilibrium payoff: one fixed target such that for every
positive accuracy a profile and a horizon threshold satisfy both target
payoff and unilateral deviation bounds at every larger finite horizon.
For fixed proper rewards, reference grand reward and own levels, the same
target, profiles and horizon thresholds work throughout the entire
coordinatewise lower-grand orthant.

A convenient strict parameter choice is

    kappa=1, L=n, e=rho_star/2,
    eta<=rho_star/8, tau<=rho_star^2/(16n).

Write Gamma_ij=Z_i({j}). The coefficientwise scalar condition is included
by taking P=Gamma^{-1} and C={1}, when that inverse is strictly positive;
nonnegative sum b^D implies the product cover. No grand-coefficient
condition or lower bound on b_i^D is needed here.
The theorem can apply when NO positive scalar reward ledger has nonnegative
joining loss on every proper coalition.

## 2. Conjecture-facing change and strategic inputs

The producer replaces a common positive coalitionwise joining-loss ledger
by a finite cover of independent product hazards. It allows an arbitrary
invertible positive coordinate matrix and needs only upper bounds on its
transformed joining losses. Quiet-root selection removes every condition on
the transformed grand reward. The prescribed profiles avoid that coalition,
which gives an unbounded downward closure of the covered reward class.

Every strategic input is produced: finite Nash existence supplies roots,
the raw product cover selects a valid inequality at each root, the common
cone supplies a single global size function, and finite backward induction
supplies the clocks. A terminal comparison and an explicit one-atom repair
produce actual absorbing profiles. No recurrent orbit, continuous selector,
actual minimizing source, equilibrium tail or punishment is assumed.

The exact Fin4 table below lies outside every positive coalitionwise scalar
ledger. After adding own levels one, its entire stationary cube has a
positive debt gap, including approximate stationary limits. It also excludes
every sure-at-first-stage equilibrium with any
actual continuation. These are concrete coverage comparisons, not a claim
that all nonstationary architectures have been classified. The universal
Fin4 problem remains open outside the stated raw region.

## 3. Exact root equations and the common size function

Let q be a Nash equilibrium of a one-stage reference stop/continue game with
continuation payoff w. Write h=product_i(1-q_i), R=sum_D p_D Zhat(D),
U'=R+h w, and let Q_i be the offer when player i certainly quits. Then

    s=U'-Q>=0,                 q_i s_i=0,
    R-Q=sum_D p_D ell^D.

For the second identity, coordinate i is the sum over opponent coalitions
E of (1-q_i)Pr(E)[Zhat_i(E)-Zhat_i(E union{i})]. The empty E contributes
zero because both the live reward and own singleton are zero; each other
term is p_E ell_i^E. With x=P w, x'=P U', A=P R and z=P s,

    x'=h x+A,                 z=h x+B.

When q has a quiet owner, p_I=0, so every coefficient in A is a proper
coalition coefficient covered by the raw hypotheses.

The size function remains a=sum x throughout the entire construction.
The selected ledger c may change from root to root, but neither the size
function nor the angular region changes. On the common signed cone

    a>0, x_i>=-kappa a,

the definition of m(c) gives c dot x>=m(c)a. Also z=P s>=0 and
c dot z<=C(c) sum z. Thus a covering ledger at this root gives

    c dot z=h(c dot x)+c dot B>=m(c)h a,
    sum z>=m(c)h a/C(c),
    z_i>=rho_star h a.

This is the required common lower bound. There is no amortized loss when
the covering ledger changes.

## 4. Every continuation in the cone admits a quiet Nash root

Fix w with a=sum P w>0 and x_i>=-kappa a. For t>0, modify the reference
one-stage rewards by subtracting t from player i's reward whenever i is
among the quitters. This includes its own singleton. Keep continuation w
fixed. The modified finite game has a Nash equilibrium.

Let R^t,Q^t,U^t be its root quantities. Directly,

    R^t_i=R_i-t q_i, Q^t_i=Q_i-t,
    U^t-Q^t=h w+sum_D p_D ell^D+t(1-q).

Suppose every owner is active, q_i>0. Complementarity gives U^t-Q^t=0.
Choose a covering c and put omega=c^T P, which is strictly positive.
Then

    0=h(c dot x)+c dot B+t sum_i omega_i(1-q_i).

If q differs from the all-sure vector, the last term is strictly positive,
while the first two terms are nonnegative. Contradiction.

The all-sure vector is also impossible. Apply the product cover to the pure
coalition I minus{i}. Its joining-loss vector has only coordinate i, so
c dot b=(c^T P)_i ell_i>=0 for some positive c forces ell_i>=0. At all-sure,
player i gains ell_i+t>0 by withdrawing and continuing. Therefore every
Nash root of every penalized game has at least one zero hazard.

Take t down to zero and a convergent subsequence of these roots. Nash
inequalities are continuous, and the finite union of zero-coordinate faces
is closed. The limit is a Nash root of the ORIGINAL reference game with
at least one quiet owner. No continuous selector is asserted or required.

## 5. The common global collar expands survival-adjusted size

Assume additionally min_i x_i<=e a and choose a quiet root from Section 4.
If h=0, it already absorbs and the iteration stops. Suppose h>0.
Choose i with x_i<=e a. Section 3 gives

    B_i=z_i-h x_i>=(rho_star-e)h a,
    sum A>=((rho_star-e)/tau)h a.

Put g=1+(rho_star-e)/tau>1. Then

    a'=h a+sum A>=g h a.

Every coordinate satisfies x'_i>=-kappa a'. For a quiet owner j, every
positive-probability coalition omits j, so A_j<=eta sum A. The signed
lower bound on the input gives x_j<=L a. Consequently

    min_i x'_i/a'<=eta+(L-eta)/g<=e.

Thus the same collar is invariant under the selected roots. If nu denotes
survival to the existing finite chain's terminal annotation, prefixing gives
nu'=h nu and

    a'/nu'>=g a/nu.

All estimates are exact at arbitrary hazard size. No local expansion,
selected recurrent word, or assumed return is used.

## 6. Finite construction, virtual-terminal removal, and absorption

Choose a player j and epsilon>0. Start a horizon-zero finite game with
forced terminal payoff w0=epsilon P^{-1}e_j. Then x0=epsilon e_j lies in
the collar and a0=epsilon. Repeatedly prepend quiet Nash roots supplied
by Section 4. Backward induction makes every finite chain an exact Nash
profile for its forced-terminal finite game. Every prescribed coalition
at every root is proper.

If a root has h=0, the chain absorbs. Otherwise its terminal survival nu_k
satisfies a_k/nu_k>=g^k epsilon. Prescribed payoffs are convex combinations
of proper-coalition rewards and w0, so a_k is bounded above independently
of k. Hence nu_k tends to zero. No infinite-chain realization is needed.

Replace the forced terminal payoff by continuing forever in the native
infinite game. Prescribed and unilateral payoffs each change by at most
||w0||_infinity: after the finite chain all opponents continue, and a
remaining deviator can quit alone or Never, both worth native zero.
Each player's native debt is therefore at most 2||w0||_infinity,
and summed full debt is at most 2n||w0||_infinity.

If absorption has not yet occurred, move the smallest individual Never
atom to a solo date after the chain. Its mass is at most nu_k^{1/n}; the
new prescribed profile absorbs and still never realizes the grand coalition.
The full-debt perturbation is at most 2R(2n-1)nu_k^{1/n}, with R a finite
absolute bound on the reference rewards. Indeed coupling the old and new
date laws changes every prescribed payoff by at most 2R times the moved
mass. It changes each other owner's complete response cap by the same bound,
uniformly over all deviations. The mover's cap is unchanged because its
opponents are unchanged. Summing gives the displayed 2n-1 factor.
Let k increase and then epsilon decrease.
The infimum absorbing reference debt is zero.

Now lower any grand reward coordinates. Prescribed payoffs of these laws
are unchanged, and every unilateral payoff weakly decreases. Therefore
the same profiles have no larger full debt in the actual table. This gives
the claimed unbounded downward-grand closure directly.

On absorbing prescribed laws, adding nonnegative own levels s_i to every
nonempty reward shifts both prescribed payoffs and complete response caps
by s_i. Finite replies always absorb; late finite deadlines dominate the
literal Never reply when s_i>=0. Thus full debt agrees with native debt.
For completeness the fixed-target and shared-horizon conclusion can be
seen directly on the constructed profiles. Choose a sequence with debt
tending to zero and extract a convergent subsequence of its bounded
prescribed payoff vectors, with limit v. Each profile has a finite date N
after which every prescribed stopping law is either already stopped or
Never. Against a unilateral deviation, conditional on survival past N all
opponents continue forever. Quitting later alone gives s_i>=0. Replacing
the deviator's finite-horizon late behavior by quitting immediately after N
can only increase its terminal contribution on that event. Before N,
terminal and horizon-H average weights differ by at most (N+1)/H times
the reference reward bound. This bound is uniform over all deviations.
Prescribed finite-horizon payoffs converge to the selected terminal payoffs
with the same finite-calendar estimate. Thus each accuracy admits a member
of the subsequence and a finite H threshold proving the uniform contract
with the fixed target v.

Finally every prescribed finite-horizon payoff of these profiles is
unchanged by decreasing grand rewards, while every unilateral finite-horizon
payoff weakly decreases pointwise. The reference target, chosen profiles
and horizon thresholds therefore work simultaneously for all finite
coordinatewise grand decreases, with no common lower bound on those rewards.
The cited terminal-all-errors consumer supplies the same semantic endpoint;
the product-cover producer is the new ordinary mathematics.

## 7. Why this removes the old scalar joining-loss restriction

For P=Gamma^{-1}, a scalar reward ledger omega>0 has coalition joining-loss
omega dot ell^D. The old fixed ledger is omega=1^T P. The present theorem
allows different positive omega=c^T P on different product hazards.
The example below has no positive omega satisfying omega dot ell^D>=0
for all proper D, so no fixed positive reweighting recovers that condition.
The product restriction is essential: arbitrary mixtures of pure coalition
laws would destroy the cover, whereas independent product laws obey the
quadratic inequalities in Section 8.

## 8. A finite two-ledger rectangle certificate

Fix distinct owners k,i,j with {k,i,j} proper. Choose two admissible
coefficient ledgers c^+,c^-.
Suppose, for some d>0, all proper-coalition coefficients outside
D={k},{k,i},{k,j},{k,i,j} are nonnegative for BOTH ledgers, while

    c^+ dot b^{k}, c^- dot b^{k} >= d,
    c^+ dot b^{k,i,j}, c^- dot b^{k,i,j} >= d,
    (c^+ dot b^{k,i}, c^- dot b^{k,i}) >= (-2d,d),
    (c^+ dot b^{k,j}, c^- dot b^{k,j}) >= (d,-2d).

At positive odds x=z_i,y=z_j, the two sums are bounded below by

    d z_k(1+xy-2x+y), d z_k(1+xy+x-2y).

If x<=y the first is at least d z_k(1+x^2-x)>0; if x>=y the second
is at least d z_k(1+y^2-y)>0. In fact the larger bracket is at least
(1+x)(1+y)/4. This proves the product cover using finitely many explicit
raw inequalities. Finite C and continuity cover all hazard boundaries.

The coefficient certificate admits strict perturbations: one may replace
the negative lower bounds by -9d/4 and positive lower bounds by 3d/4 while
retaining the two good lower bounds d. The chosen bracket then dominates
1+x^2-(3/2)x, whose minimum is 7/16>0. Thus a strict interior version is
available without imposing exact cancellation identities.


## 9. Exact Fin4 separating table

### Literal table

Players are 0,1,2,3. Set

    Gamma = [ 0 -2 -5  4
             -6  0 -4  6
              1  3  0 -5
              1 -1  4  0 ],
    M=Gamma^-1,
    lambda=1^T M=(95,46,127,170)/21,
    beta=10^-6, alpha=1-beta, delta=10^-24,
    d=1/100, R=3/(2d)=150, r=d/(3lambda_3)=7/17000.

Define five positive exact numbers

    A=delta(R lambda_3-1/2)/lambda_2,
    B=delta R,
    C=delta(R lambda_3+1/2)/lambda_1,
    E=delta lambda_2(1+r),
    F=delta lambda_1.

They satisfy E<6B. Prescribe pair joining-loss vectors

    ell01=(0,0,A,-B),
    ell02=(0,-C,0,B),
    ell03=(0,E,-F,0),
    ell12=(0,0,0,delta),
    ell13=(0,0,delta,0),
    ell23=(0,delta,0,0).

The native rewards are defined as follows. Singletons are Gamma columns.
Every pair reward is alpha Gamma 1_D. For a triple D, its participant
coordinate i in D is

    Z_i(D)=alpha(Gamma 1_D)_i - ell_i^(D minus {i}),

while its one passive coordinate is alpha(Gamma 1_D)_i-2delta.
The grand reward is alpha Gamma 1-3delta 1. This defines all sixty native
reward coordinates, including the four own zeros. Equivalently the triple
correction vectors, relative to alpha Gamma 1_D, are

    R012=(0,C,-A,-2delta),
    R013=(0,-E,-2delta,B),
    R023=(0,-2delta,F,-B),
    R123=(-2delta,-delta,-delta,-delta).

The actual joining losses are exactly the six pair vectors displayed
above, singleton losses beta Gamma[:,j], and triple losses delta e_i for
the missing owner i. The grand joining loss is zero. Every reward has
absolute value below100. Adding a common own-singleton level one gives an
original table with strictly positive own levels and unchanged native debt
on every absorbing profile.

### Strict finite-ledger cover

Choose two positive reward ledgers

    omega^- = lambda-d e_3^T,
    omega^+ = lambda+d e_3^T.

Their common-chart coefficient rows are

    c^- = omega^- Gamma=(99/100,101/100,24/25,1),
    c^+ = omega^+ Gamma=(101/100,99/100,26/25,1).

The weighted coefficients of pairs01,02, divided by delta, are respectively

                01    02
    omega^-      1    -2
    omega^+     -2     1.

Both ledgers give strictly positive coefficient to pair03, because
omega^r_1=lambda_1 and omega^r_2=lambda_2, and

    omega^r ell03=delta lambda_1 lambda_2 r>0.

Every other proper-coalition coefficient is strictly positive under both
ledgers. For singleton0, beta min(c^-_0,c^+_0)>delta. For triple012,
min(omega^-_3,omega^+_3)>1. Thus, for nonnegative odds z and x=z1,y=z2,

    sum_D z_D omega^- ell^D
        >= delta z0(1+xy+x-2y),
    sum_D z_D omega^+ ell^D
        >= delta z0(1+xy-2x+y),

with all discarded monomials nonnegative. The exact cover inequality is

    max(1+xy+x-2y,1+xy-2x+y)
       =(1+x)(1+y)-3min(x,y)
       >=(1+x)(1+y)/4.

For the last inequality, if x<=y then x/[(1+x)(1+y)]<=x/(1+x)^2<=1/4;
the other case is symmetric. Hence at least one ledger is strictly positive
whenever z0>0. When z0=0 and z is nonzero, the positive singleton terms
supply strict positivity. In particular every proper nontrivial product
root admits a favorable ledger; no selected root is assumed.

The uniform quarter margin and the strictly positive other coefficients
make this cover stable under small independent raw-reward perturbations.
The ledger vectors may be held fixed as reward rows; their positive
common-chart rows vary continuously with Gamma.

### No common positive coefficient ledger exists

The obstruction is stronger than failure of the original lambda. Namely,

    ell01+ell02+(C/E)ell03 = -delta/(2lambda_2) e_2.

All three multipliers are strictly positive. Therefore no strictly positive
reward row omega can satisfy omega ell^D>=0 for every coalition D.
In particular no change of positive scalar ledger rescues the older
coalition-by-coalition condition. Also

    lambda ell01=lambda ell02=-delta/2<0,

so the fixed-sum coefficient condition sum b^D>=0 rejects the table.

The obstruction is open. In the fixed signs above, the first two losses
would require

    omega1/omega2 <= (lambda1/lambda2)(1-r)/(1+r),

whereas pair03 requires

    omega1/omega2 >= (lambda1/lambda2)/(1+r).

The strict gap persists under sufficiently small coefficient perturbations.
All three loss vectors are structurally zero at owner0, so no arbitrarily
large owner0 weight can evade it.

### Exact common-chart bounds

Use kappa=1, so L=4. For every x with sum x=a>0 and x_i>=-a,

    c^- x >=(21/25)a,   c^+ x >=(21/25)a,
    max_{r,i} c_i^r=26/25.

Indeed the exact minimum of c x/a on this signed simplex is
5 min_i c_i-sum_i c_i. Also rho=3/95. Hence an admissible common lower bound for the positive-image
constant is

    rho_* = rho (21/25)/(26/25) = 63/2470.

Choose eta=rho_*/8, e=rho_*/2, tau=rho_*^2/64. Exact rational checking gives,
for every nonempty D with a^D=MZ(D), b^D=M ell^D,

    sum a^D>0,
    a_i^D> -sum a^D,
    a_j^D<eta sum a^D       whenever j outside D,
    |b_i^D|<tau sum a^D.

The scalar output collar inequality is strict. Thus every remaining raw
condition of the adaptive theorem has margin, as does its ledger cover.

### Positive original stationary debt gap

All proper supports of size one or two fail. A singleton support has an
outsider with Gamma_ij<0, whose Quit offer exceeds the stationary payoff.
For a two-player support, stationary indifference at i would require
Gamma_ij q_j(alpha q_j-1)=0, impossible for 0<q_j<1. Sure boundaries are
excluded separately in the sure-root census below.

For a proper stationary triple S, put

    H_i=product_{j in S minus i}(1-q_j),
    v_i=alpha q_i+beta q_i/(1-q_i)>0,
    T_i=(1-H_i)product_{j in S minus i} q_j/(1-q_j)>0.

Passive pairs have their baseline values, so exact stationarity reads

    Gamma_SS v=(R_i(S) T_i)_{i in S},

where R_i(S) is the participant triple correction.
For012, row0 is -2v1-5v2=0, impossible. For023, row3 is
v0+4v2=-B T3<0, impossible. For123, the principal inverse is strictly
positive but its right-hand side is strictly negative, impossible.
For013, row0 gives v1=2v3. The other rows give

    v0-v3=(E/6)T1,     v0-v1=B T3,
    v3=(E/6)T1-B T3.

Since v(q) is increasing, v1>v3 implies q1>q3 and T1<T3. Since E<6B,
the final displayed expression is negative, contradiction.

A proper full-support stationary root is also impossible. Its inverse
coordinate x=M R(q)/(1-h) lies in the signed cone and has positive mass.
A favorable ledger gives c^r M(U-Q)=h c^r x+c^r B>0,
whereas every active owner's Nash equality would give U-Q=0.

Gamma is R0: if v>=0, Gamma v>=0 and v_i(Gamma v)_i=0 for all i,
write u=Gamma v. If u is nonzero, M>0 gives v=M u strictly positive,
forcing u=0 by complementarity, a contradiction. If u=0, invertibility
already gives v=0. A vanishing-debt stationary sequence tending to q=0 would,
after normalizing q/sum q, give v>=0, sum v=1, Gamma v>=0 and
v_i(Gamma v)_i=0. Immediate Quit supplies Gamma v>=0; literal Never
supplies the complementary equalities: its limiting payoff is
(Gamma v)_i/(1-v_i). A singleton limiting hazard direction is excluded
already by the negative outsider entry in that singleton column, so every
denominator is positive. This contradicts R0. Away from q=0, vanishing
full debt makes immediate Quit and Continue-then-prescribed deviations
unprofitable; a limiting nonzero q would therefore be a forbidden exact
stationary root. These arguments give a positive full-debt gap over native
stationary q!=0. The native q=0 profile itself has zero debt. For the
original table r=Z+1, every q!=0 is absorbing and has the same debt; q=0
has debt4. Hence the entire ORIGINAL stationary cube has a positive gap.

### Every sure-at-first-stage root and every actual tail are excluded

Write g_i=Quit_i-Continue_i. Whenever another owner quits surely, g_i is
independent of the continuation. Positive g_i forces q_i=1 and negative
g_i forces q_i=0. Every actual full response cap is at least-100.

On face q1=1, g2 is a strictly negative convex combination of
(-3beta,-A,-delta,-delta), so q2=0. Then

    g3=beta(1-q0)+B q0>0,

forcing q3=1, after which g1=-6beta(1-q0)-E q0<0 contradicts q1=1.

On face q2=1, g3 is a strictly negative convex combination of
(-4beta,-B,-delta,-delta), so q3=0. Then

    g1=4beta(1-q0)+C q0>0,

forcing q1=1, after which g2=-3beta(1-q0)-A q0<0 is impossible.

On face q3=1, g1 is a strictly negative convex combination of
(-6beta,-E,-delta,-delta), so q1=0. Now g0=-4beta(1-q2). If q2<1,
this forces q0=0, after which g2=5beta>0 forces q2=1, a contradiction.
Thus q2=1; then g3=-4beta(1-q0)-B q0<0 contradicts q3=1.

It remains q0=1, with the other hazards strictly below one. If all are
positive, their indifference plus owner0's sure action gives R-Q=0.
But the strict ledger cover still holds on this face: factor the positive
product product_{j=1}^3(1-q_j) from the sums over coalitions containing0,
and apply the same rectangle inequality. Some omega^r(R-Q)>0, a
contradiction. Thus some other owner is quiet. If q1=0, then

g3=-beta(1-q2)-B q2<0 forces q3=0; g2=-beta<0 then forces q2=0,
and g1=6beta>0 contradicts q1=0. If q3=0, g2<0 forces q2=0,
g1=6beta>0 forces q1=1, and g3=B>0 contradicts q3=0.
Consequently q2=0 and the other two indifferences uniquely give

    q1=beta/(beta+B),     q3=6beta/(6beta+E).

The participant and passive row0 rewards on this support have no higher
correction. Its sure-Quit condition therefore requires continuation cap

    m0 <= beta^2(2/B-24/E)
        =-8539201480000000000/2159889 < -100.

No actual tail has such a full response cap. The same lower bound holds
for a punishment value defined as an infimum of actual full response caps.
Thus no equilibrium can have a sure quitter at the FIRST stage, regardless
of the actual behavioral continuation. Compactness of that sure boundary
and the bounded full-cap box gives a positive full-debt gap for this
architecture. This does not exclude profiles whose first sure stage is
late: the producer's final solo repair is precisely such a profile.

### Further coverage comparisons

Every pair participant reward remains J_ij=alpha Gamma_ij. Hence the old
positive-inverse paired producer requiring p_i=J_ij>=0 and p_i-Gamma_ij>0
fails for every possible scheduled partner. Gamma has only one mutually
negative pair, so no negative perfect matching exists.

The ordered-anchor test fails because the positive-entry graph of Gamma
is strongly connected. Its passive singleton guards force the marked set
to be all players; its first-block pair guards force the first block also
to contain all players. The mutually positive pair03 then violates every
positive weighted first-block inequality.

Higher-support product-lowness fails on support023 at
q0=3/5,q2=1/20,q3=1/10,q1=0: all three participant Quit offers are strictly
positive (checked rationally). Thus the existing finite-ledger producer
that also requires proper-support product-lowness does not apply.

The only nonnegative-inverse principal triple is123, whose exterior
inverse row is (-17/52,-31/26,-41/26), so the raw passive-child criterion
also rejects. The positive inverse also defeats nonzero nonnegative scalar or
support-filtered weights with smaller support: w^T Gamma>=0 and M>0 imply
w^T=(w^T Gamma)M>0. A weighted inserted-floor criterion supported on pair03
would need this singleton inequality, which forces full support and is
impossible. A larger-trap condition demanding negative outside participant
premiums fails on trap123 at singleton1, where J21+J31=2alpha>0. The
mixed-support upper-or-charge criterion fails on the mutually positive
pair03: no positive participant weights make its upper average nonpositive,
and the alternative boxed-charge branch requires at least three owners.
The same pair already violates proper-support product-lowness; the explicit
triple test above rejects versions allowing exceptional same-sign pairs.
These comparisons cover their complete choices of weights and supports.
They do not assert a classification of all nonstationary strategies.

## 10. The separating table's entire lower-grand orthant

Keep every proper reward of Section 9 fixed and replace the reference
grand reward by Z_i(I)-Delta_i, for arbitrary finite Delta_i>=0. Section 6
already gives the same UE target and witnesses throughout this family.
The following comparisons show that the scalar-ledger, stationary and
sure-at-first-stage exclusions persist as well.

### Full-support stationary comparison is pointwise monotone

For a stationary hazard vector q, let H_i=product_{j!=i}(1-q_j), let Q_i be
its Quit offer, and let P_i be its passive Continue absorption contribution.
Define the stationary incentive polynomial

    F_i(q)=(1-H_i)Q_i-P_i.

If h=product_i(1-q_i)<1 and U is its stationary payoff, the identity

    U_i-Q_i=-(1-q_i)F_i/(1-h)

holds. At a stationary Nash point, every active owner must have F_i>=0;
a properly mixing owner requires F_i=0.

At every full-support q for the REFERENCE fixture, at least one F_i is
strictly negative. For h>0, suppose contrariwise all F_i>=0. Then U-Q<=0.
Its coefficient x=M U lies in the shared signed cone with positive mass,
because the reference fixture satisfies the stronger all-coalition bounds.
The adaptive cover gives a c with

    c dot M(U-Q)=h c dot x+c dot B>0,

contradicting M(U-Q)<=0. When h=0 and q is not all-sure, the strict
cover remains valid.
If a sure owner is1,2 or3, at most one of the two bad coalitions01,02
can occur. Choose the ledger positive on that coalition; every realized
proper coefficient is then positive, and some proper coalition has positive
probability. If0 is the sole sure owner, factor the other owners' positive
survival probabilities and apply the strict rectangle bound. In either
case c dot B>0 gives the contradiction even with h=0. At all-sure, every
withdrawal is strictly profitable, because
each codimension-one joining loss is delta>0.

Lowering the grand reward leaves P_i unchanged and gives exactly

    F_i^actual(q)=F_i^reference(q)
       -(1-H_i) product_{j!=i}q_j Delta_i <=F_i^reference(q).

Consequently the strictly negative field remains negative at every full
support. No full-support stationary Nash point exists anywhere in the
lower-grand orthant.

All proper-support active equations are unchanged, since an active owner
cannot create the grand coalition when another owner is always quiet.
Thus the exact singleton, pair, and triple contradictions in the reference
fixture remain valid. For each fixed finite Delta, the q->0 normalized
hazard argument still sees the same R0 singleton matrix. No vanishing-debt
sequence of nonzero stationary hazards can accumulate at AllContinue. Each
table therefore retains a positive ORIGINAL stationary debt gap. This is
claimed separately for each fixed table, not uniformly over the orthant.

### Full-support sure roots and all remaining sure faces

At a full-support sure root, prescribed payoff R equals every active
owner's Quit offer, independently of the continuation: the sure owner's
equality is automatic, and every other owner is indifferent against another
sure quitter. Hence R-Q=0. The reference strict adaptive cover rules this out.

A grand decrease changes only codimension-one joining losses, adding
Delta_i e_i to ell^{I minus{i}}. Since both reward ledgers are positive,
each ledger's product polynomial weakly increases. Thus strict cover and
the full-support sure-root exclusion persist throughout the lower-grand family.
The all-sure vector remains excluded because all withdrawals become more
attractive.

In the other sure-face proofs, every negative comparison coefficient
involving the grand coalition becomes more negative. Every positive
comparison used to force a hazard to one occurs after a quiet owner has
already been established, so it uses only unchanged proper rewards. The
same sign-forcing proofs therefore reduce every possible sure root to

    q0=1, q2=0,
    q1=beta/(beta+B), q3=6beta/(6beta+E).

The sure owner's comparison involves only proper coalitions, so its required
continuation cap is unchanged:

    m0<=beta^2(2/B-24/E)<-100.

Every actual continuation has full response cap at least -100 UNIFORMLY
over the entire lower-grand orthant. Choose literal Never: because the owner
never joins, the realized coalition is always proper or Never, so its reward
is at least -100. This lower bound does not use the minimum grand reward.
All caps are also at most100, since grand decreases cannot increase any
reward. Thus the same compact cap box applies to the whole family.

No table in the lower-grand orthant admits an equilibrium with a sure
quitter at its first stage followed by any actual behavioral continuation.
For each table, compactness yields a strict positive gap against that
entire architecture.

### The scalar-ledger obstruction persists

The no-common-positive-ledger certificate uses only pair losses, hence only
pair and triple reward coordinates. They are unchanged by grand decreases:

    ell01+ell02+(C/E)ell03=-delta/(2lambda_2)e_2.

Therefore every table in the unbounded family remains outside every
coalitionwise positive scalar-ledger condition. The proper-triple positive
Quit-offer witness and the ordered-anchor rejection are likewise unchanged.
Prescribed continuation payoffs themselves need not remain in a common box;
the bound here is on full response caps, using the literal Never option.

## 11. Reproducible exact arithmetic

Run this complete Python3/SymPy block. All arithmetic is rational; the
continuum support proofs above supply completeness. No external inputs are used.

```python
from itertools import combinations
import sympy as s
I=range(4)
G=s.Matrix([[0,-2,-5,4],[-6,0,-4,6],[1,3,0,-5],[1,-1,4,0]])
M=G.inv(); one=s.ones(4,1); lam=(one.T*M)
assert G.det()==42 and all(v>0 for v in M)
assert lam==s.Matrix([[95,46,127,170]])/21
beta=s.Rational(1,10**6); alpha=1-beta; delta=s.Rational(1,10**24)
d=s.Rational(1,100); R=3/(2*d); r=d/(3*lam[3])
A=delta*(R*lam[3]-s.Rational(1,2))/lam[2]
B=delta*R
C=delta*(R*lam[3]+s.Rational(1,2))/lam[1]
E=delta*lam[2]*(1+r)
Fv=delta*lam[1]
loss={frozenset((0,1)):s.Matrix([0,0,A,-B]),
      frozenset((0,2)):s.Matrix([0,-C,0,B]),
      frozenset((0,3)):s.Matrix([0,E,-Fv,0]),
      frozenset((1,2)):s.Matrix([0,0,0,delta]),
      frozenset((1,3)):s.Matrix([0,0,delta,0]),
      frozenset((2,3)):s.Matrix([0,delta,0,0])}
Z={}
for k in range(1,5):
 for D0 in combinations(I,k):
  D=frozenset(D0); indicator=s.Matrix([int(i in D) for i in I])
  if k==1: Z[D]=G*indicator
  else:
   Z[D]=alpha*G*indicator
   if k==3:
    for i in I:
     if i in D: Z[D][i]-=loss[D-{i}][i]
     else: Z[D][i]-=2*delta
   if k==4: Z[D]-=3*delta*one
actual_loss={D:s.Matrix([0 if i in D else Z[D][i]-Z[D|{i}][i] for i in I]) for D in Z}
assert all(actual_loss[D]==v for D,v in loss.items())
assert all(actual_loss[frozenset((j,))]==beta*G[:,j] for j in I)
assert all(actual_loss[D]==s.Matrix([delta*int(i not in D) for i in I]) for D in Z if len(D)==3)
assert actual_loss[frozenset(I)]==s.zeros(4,1)
wm=lam.copy();wp=lam.copy();wm[3]-=d;wp[3]+=d
cm=wm*G;cp=wp*G
assert cm==s.Matrix([[s.Rational(99,100),s.Rational(101,100),s.Rational(24,25),1]])
assert cp==s.Matrix([[s.Rational(101,100),s.Rational(99,100),s.Rational(26,25),1]])
assert all(c>0 for c in list(cm)+list(cp))
# Exact rectangle coefficients, in order 01,02.
assert [s.simplify((w*loss[D])[0]/delta) for w in (wm,wp) for D in (frozenset((0,1)),frozenset((0,2)))]==[1,-2,-2,1]
assert all((w*loss[frozenset((0,3))])[0]>0 for w in (wm,wp))
assert all((w*actual_loss[D])[0]>0 for w in (wm,wp) for D in Z if D not in (frozenset((0,1)),frozenset((0,2)),frozenset(I)))
assert beta*min(cm[0],cp[0])>delta
assert min(wm[3],wp[3])>1
# A positive linear combination of the three pair loss vectors is negative.
t=C/E
assert s.simplify(loss[frozenset((0,1))]+loss[frozenset((0,2))]+t*loss[frozenset((0,3))])==s.Matrix([0,0,-delta/(2*lam[2]),0])
# No original fixed-sum ledger: both critical pair sums are strictly negative.
assert (lam*loss[frozenset((0,1))])[0]==-delta/2
assert (lam*loss[frozenset((0,2))])[0]==-delta/2
rho=min(M[i,j]/lam[j] for i in I for j in I)
assert rho==s.Rational(3,95)
m=s.Rational(21,25); cmax=s.Rational(26,25)
assert all(5*min(c)-sum(c)>=m and max(c)<=cmax for c in (cm,cp))
rho_eff=rho*m/cmax
assert rho_eff==s.Rational(63,2470)
eta=rho_eff/8; e=rho_eff/2; tau=rho_eff**2/64
for D,z in Z.items():
 a=M*z; asum=sum(a); b=M*actual_loss[D]
 assert asum>0
 assert all(ai>-asum for ai in a)
 assert all(a[j]<eta*asum for j in I if j not in D)
 assert all(abs(bi)<tau*asum for bi in b)
assert eta+(4-eta)/(1+(rho_eff-e)/tau)<e
assert E<6*B
threshold=s.simplify(beta**2*(2/B-24/E))
assert threshold < -100
assert all(abs(v)<100 for z in Z.values() for v in z)
assert all(G.extract(S,S).det()!=0 for k in (2,3,4) for S in combinations(I,k))
assert all(any(G[i,j]<0 for i in I) for j in I)
# Proper product-lowness fails on 023.
q={0:s.Rational(3,5),1:0,2:s.Rational(1,20),3:s.Rational(1,10)}
for i in (0,2,3):
 Q=0
 for k in range(4):
  for D0 in combinations([j for j in I if j!=i],k):
   D=frozenset(D0)
   p=s.prod(q[j] if j in D else 1-q[j] for j in I if j!=i)
   Q+=p*Z[D|{i}][i]
 assert Q>0
G123=G.extract([1,2,3],[1,2,3])
assert all(v>0 for v in G123.inv())
assert G.extract([0],[1,2,3])*G123.inv()==s.Matrix([[-s.Rational(17,52),-s.Rational(31,26),-s.Rational(41,26)]])
for S in combinations(I,3):
 if S!=(1,2,3): assert any(v<0 for v in G.extract(S,S).inv())
for start in I:
 seen={start}
 for _ in I: seen|={j for i in seen for j in I if G[i,j]>0}
 assert seen==set(I)
assert alpha*(G[2,1]+G[3,1])==2*alpha>0
print('PASS: exact reward realization, two-ledger cover coefficients, no common positive ledger, signed cone, smallness, stationary algebra guards, sure-tail threshold, product-low rejection')
print('rho_eff=',rho_eff,' tau=',tau,' E/delta=',E/delta)
print('sure0 cap threshold=',threshold)
print('lambda=',lam)
```

## 12. Open coverage, source correspondence and handoff

The signed-cone and upper-loss inequalities are strict at the reference
table, apart from structural own-zero and grand-loss identities. The
rectangle quarter margin and the positive remaining coefficients give a
strict finite-coefficient version of the product cover. For example,
slightly decrease its good coefficient lower bounds while allowing the
bad coefficients to vary within the relaxed bounds of Section 8. Keep
the two reward rows omega fixed; their coefficient rows omega Gamma
remain positive with m(c)>0 under small perturbations. Therefore a whole
open neighborhood in all free native rewards is accepted. Original own
levels are all1 and remain positive under small independent variations of
all sixty original reward entries. This is a full-dimensional UE region.

The separation is also open. The incompatible weight-ratio inequalities
have a strict gap. A uniform reward change of at most xi changes every
prescribed payoff and every complete response cap by at most xi, hence
summed debt by at most2n xi. The positive stationary gap consequently
persists. Compactness of the sure boundary times its full-cap box preserves
the sure-at-first-stage exclusion. No limiting inference here treats a
bounded sample of roots as an exhaustive census; the support proofs above
give completeness.

The named finite mixed-Nash input is `exists_isZeroQuittingRootNash`
(`UniformEquilibrium/Quitting/Root/NashExistence.lean`). It permits any
finite reward table and fixed continuation, including the participant-penalized
tables used before taking a limit. The exact all-behavior prefix equation is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`): the cap is the
maximum of Quit and Continue carrying the owner's actual continuation cap.
It confirms why a supplied prescribed tail payoff is insufficient in the
sure-root comparisons.

The late-deadline input is
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile`
(`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`).
Its limit is the literal Never payoff plus the opponents' Never probability
times the own singleton reward. Thus own-zero native rewards allow the
Never response to be recovered by finite deadlines, and nonnegative
original own levels justify the row translation used above.

The fixed-target consumer is
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Its input is an actual terminal approximate Nash profile at each positive
error, against all behavioral deviations; its conclusion is one fixed
uniform-equilibrium payoff. Sections 3–6 construct those inputs directly,
and Section 6 explains the stronger simultaneous lower-grand transfer.

The new formalization targets are the finite raw product-cover condition,
participant-penalty quiet-root lemma, shared signed cone and global growth
of survival-adjusted size. They use finite sums, finite Nash existence and
compactness of the hazard cube. A root selector, recurrent word or desired
equilibrium must not appear as an assumed structure field. The complete
finite rational test in Section 11 can be formalized independently. No Lean
files or build are supplied by this ordinary-mathematical packet.

The covered class still restricts proper-coalition geometry. In particular
if a nonempty proper coalition has a nonzero coordinatewise nonnegative
reward vector, then PZ(D) has every coordinate at least rho times its sum.
For an omitted owner this contradicts eta<rho_star<=rho. Thus even allowing
all positive matrices P and finite ledger covers cannot cover such a table
by this criterion. Other UE arguments may cover it. This identifies a real
boundary of the present mechanism, not a counterexample to UE. Arbitrary
Fin4, mixed grand-reward directions beyond an admissible reference ceiling,
and all tables outside the union of proved raw regions remain unresolved.
