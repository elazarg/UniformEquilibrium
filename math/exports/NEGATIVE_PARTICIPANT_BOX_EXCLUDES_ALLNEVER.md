# Small negative participant rewards exclude inverse-positive AllNever sources

## Statement and scope

Let I={0,1,2,3}. Independent Continue/Quit choices on natural dates determine
the first nonempty quitting coalition D; it absorbs at finite rewards Z_i(D).
Live play and the event that nobody ever quits pay zero. Own singleton
rewards Z_i({i}) are zero. An owner may replace their entire behavioral
strategy. Before absorption there is one live history per date, so these
strategies are exactly independent first-Quit laws on N union {Never}.

Write Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}) for i!=j, with zero diagonals.
Assume that Gamma satisfies:

1. Every off-diagonal entry is nonzero, det Gamma>0, and M=Gamma^-1 is
   strictly positive entrywise.
2. There is a mutually negative pair: Gamma_kl,Gamma_lk<0.

**Theorem.** There is eta(Gamma)>0 such that, for EVERY participant matrix

    -eta(Gamma)<J_ij<0 for all i!=j,

and EVERY finite completion of all other rewards, the game has an actual
infinite full Nash profile with U=B=e and original joint Never mass in(0,1).
Here U is the prescribed payoff, N_i is owner i's original Never mass,
B is the supremum payoff over every complete unilateral reply, and e is
the payoff of the unilateral literal-Never reply, which need not be zero.
The bound eta depends only on Gamma; the clock amplitude may depend on J
and all the higher rewards. This is a full negative box, not a raywise bound.

For the compact carrier C=closure{(U,B,e,N)} of actual response tuples, put
D=sum_i(B_i-U_i), nu=product_i N_i, E=C intersect{D=0}, and mu=min_E nu.
Original finite mass escaping dates is never relabeled Never. AllNever lies
in E. The theorem proves mu<1. It does not prove mu=0, absorption, UE, or
descent from a strictly positive global minimum. It is ordinary mathematics,
not a new Lean check.

## 1. A graph lemma supplies the relevant architecture

Under assumptions1 and2, either Gamma has a perfect matching of two mutually
negative pairs, or distinct p,j,k,l satisfy

    Gamma_kl,Gamma_lk<0,
    Gamma_pj<0<Gamma_jp, Gamma_kj>0, Gamma_lj>0.              (A)

Every row has both signs: an off-diagonal entry of Gamma M=Id expresses
zero as a strictly positive weighted sum of its three nonzero entries.
The identity M Gamma=Id gives the same fact for columns. Every principal
triple determinant is positive, by Jacobi's cofactor identity

    det Gamma_(I minus{r}) = det Gamma M_rr > 0.             (J)

Form the graph of mutually negative pairs. If it has no perfect matching,
every two edges intersect, so its nonempty edge set is a star or triangle.
A negative triangle forces all six entries between it and the remaining
owner positive by row/column mixing; the remaining row is then all positive.
A three-edge star has its central column entirely negative. Both are
impossible, leaving one or two negative edges.

For edges01 and02, mixing forces Gamma_03,Gamma_30>0. The entries
Gamma_13,Gamma_23 cannot both be positive, by column3 mixing. They cannot
both be negative: no further negative edge would then force Gamma_31 and
Gamma_32 positive, making row3 positive. Exactly one is negative, its reverse
is positive, and the other is positive. Use(p,j,k,l)=(1,3,0,2) or(2,3,0,1).

For the unique negative edge01, if either outside column j in{2,3} has
Gamma_0j,Gamma_1j>0, column mixing forces Gamma_pj<0 for the other outside
owner p; absence of another negative edge forces Gamma_jp>0, proving(A).
Otherwise the cross block(rows01,columns23) has at most one positive per
column and at least one per row. Relabel so

    Gamma_02>0, Gamma_03<0, Gamma_12<0, Gamma_13>0.

Then Gamma_30,Gamma_21>0. Positivity of det Gamma_012 forces Gamma_20>0,
because its two terms are Gamma_01 Gamma_12 Gamma_20 and the negative term
Gamma_02 Gamma_21 Gamma_10. Similarly det Gamma_013>0 forces Gamma_31>0.
Rows2 and3 now require Gamma_23,Gamma_32<0, a second negative edge and a
perfect matching, contradiction. This proves the graph lemma without a census.

## 2. The finite-word clock criterion

Put L=J-Gamma. For any support S of size2 or3 with L_SS invertible, define

    h_S(w)=L_SS^-1 w_S,
    (A_S w)_i=J_iS h_S(w)                  if i in S,
    (A_S w)_i=w_i+Gamma_iS h_S(w)          if i notin S.

For a finite construction-order word S1,...,Sm, put H=A_Sm...A_S1. A mode
HV=rho V, rho>1, is accepted if, with W0=V and W_r=A_Sr W_(r-1),

    h_r=L_SrSr^-1(W_(r-1))_Sr >0,
    (W_r)_i-J_i,Sr h_r>0 for every quiet i notin Sr.          (F)

Every owner must occur. These are finite linear hazard and quiet-response
tests on an eigenspace of a four-dimensional matrix. For rational data the
real characteristic roots and strict linear feasibility can be decided
algebraically. No strategic profile, selected tail or favorable root is an
input. Sections6 and7 prove that(F) produces the asserted actual Nash law.

At J=0, an active-support map has the especially simple form

    h=-Gamma_SS^-1 w_S, w_out=w+Gamma[:,S]h, (w_out)_S=0.    (Z)

The next three sections produce a simple expanding mode that passes(F)
throughout a sufficiently small negative J box.

## 3. The negative-perfect-matching case

Let S,T be a partition into mutually negative pairs, and put C=Gamma_SS,
E=Gamma_TT, W=-diag(C,E). The matrix W is a positive weighted mate
permutation, so M W is strictly positive. Perron--Frobenius supplies a
simple positive eigenvalue lambda and x>>0. Set tau=1+1/lambda>1. Then

    Gamma_ST x_T=-tau C x_S, Gamma_TS x_S=-tau E x_T.

For A=-Gamma_ST E^-1 and B0=-Gamma_TS C^-1, the vector v=-C x_S>>0 has

    B0 v=-tau E x_T>>0, A B0 v=tau^2 v.

This expanding eigenvalue rho=tau^2 is simple: the identity

    det(Gamma-tW)=det Gamma det(Id-t M W)
                =det C det E det((1+t)^2 Id-A B0)

has a simple zero at t=1/lambda, and the derivative of(1+t)^2 is nonzero.
The word S,T has full derivative H0=[[A B0,A],[0,0]], in(S,T) coordinates,
with eigenvector(v,0). Both phase hazards are positive, and the quiet gaps
are B0 v and rho v, also positive. Its simple mode and all strict tests
persist on a full J neighborhood, hence in a small negative J box.

## 4. Architecture(A): the two-pair and triple branch

Now assume there is no negative perfect matching, and choose(A). Put

    alpha=-1/Gamma_pj>0, w=e_p+alpha Gamma[:,j].

Thus w_p=w_j=0 and w_k,w_l>0. Column p has both signs and Gamma_jp>0,
so at least one of Gamma_kp,Gamma_lp is negative. Choose k as the first
coordinate exhausted by adding beta Gamma[:,p] to w, where

    beta=-w_k/Gamma_kp>0.

For Sections4 and5 assume the first hit is unique; when the two ratios
tie, Section8 supplies the construction directly. Relabel k,l accordingly.
The state z=w+beta Gamma[:,p] then has

    z_p=z_k=0, z_j=beta Gamma_jp>0, z_l>0.                   (HIT)

First suppose Gamma_pk>0. Use the construction word

    {p,j}, {k,p}, T=I minus{p}.                             (PP3)

At J=0 its first pair has hazards h_p=0,h_j=alpha and outputs w. Its second
pair has h_k=0,h_p=beta and outputs z. Put u=M_Tp/M_pp>>0; block inversion
gives Gamma_TT u=-Gamma_Tp. The final triple hazards are

    t=-Gamma_TT^-1 z_T=beta u-alpha e_j.

The k,l entries are positive. From row k of Gamma_TT u=-Gamma_Tp,

    beta u_j-alpha=-beta Gamma_kl u_l/Gamma_kj>0,

so t>>0. The total hazard vector is beta M[:,p]/M_pp. Thus the final
output is rho e_p with rho=1+beta/M_pp>1. All quiet gaps are positive:
they are(w_k,w_l), (z_j,z_l), and rho. Only the two stated pair hazards
vanish. The final triple map has only its p row nonzero; hence the return
has rank one and the expanding eigenvalue rho is simple.

Continue this eigenmode analytically for small J, normalizing V_p=1.
All already-strict hazards and quiet gaps persist on a full neighborhood.
The final triple still has t>>0. Its output gives the EXACT identity

    rho V_j=sum_(m in T) J_jm t_m<0

for every strictly negative off-diagonal J. Therefore the first missing
hazard h_(1,p)=V_j/L_jp is positive since L_jp<0. Its first output satisfies
(W1)_p=J_pj h_(1,j)<0. Consequently the second missing hazard
h_(2,k)=(W1)_p/L_pk is positive, since L_pk<0 for small J. Thus(F) holds
uniformly throughout some negative J box; no raywise lower margin is needed.

## 5. Architecture(A): the pair and two-triple branch

Suppose instead Gamma_pk<0. Row p has both signs; since Gamma_pj<0,
this forces Gamma_pl>0. Replace the middle pair by a triple:

    {p,j}, U=I minus{j}, T=I minus{p}.                      (P33)

At the state w after the first pair, let q=-Gamma_UU^-1 w_U and
D_U=det Gamma_UU>0. Write w=e_p+alpha Gamma[:,j]. The block inverse
identity and the diagonal cofactor of Gamma_UU give

    q_p=Gamma_kl Gamma_lk/D_U+alpha M_pj/M_jj>0.

Cramer's rule gives

    q_k=Gamma_pl(Gamma_lp w_k-Gamma_kp w_l)/D_U>0.

If Gamma_lp>=0, this is immediate. If Gamma_lp<0, it is precisely the
strict first-hit inequality for k. The p indifference equation gives

    q_l=-Gamma_pk q_k/Gamma_pl>0.

The only remaining output coordinate is j. Applying M to the update and
reading its j coordinate yields

    w+Gamma[:,U]q=r e_j, r=(M_jp+alpha)/M_jj>0.

The final triple T at r e_j has hazards, in order(j,k,l),

    t=(r/det Gamma_TT)
       (Gamma_kl Gamma_lk, -Gamma_kl Gamma_lj, -Gamma_kj Gamma_lk)>>0.

Its output is rho e_p. The total hazard vector alpha e_j+q+t satisfies

    alpha e_j+q+t=(rho-1)M[:,p].

Reading coordinate p gives rho=1+q_p/M_pp>1. All quiet gaps are strictly
positive: they are(w_k,w_l), r, and rho. Only the first pair hazard of p
vanishes. The final triple again makes the return rank one with a simple
expanding mode. Under small negative J, all strict margins persist and
the exact identity rho V_j=sum_(m in T)J_jm t_m<0 makes that missing hazard
V_j/L_jp positive. This proves(F) on a full small negative J box.

Both branches are essential: the first exhausted k need not have
Gamma_pk>0. No continuation value is assumed coordinatewise nonnegative
after J is perturbed. Quiet inequalities, not tail positivity, enforce Nash.

## 6. Actual root maps, including arbitrary higher rewards

For root hazards q, let H_i(q)=product_(j!=i)(1-q_j). Let P_i(q) be the
expected reward Z_i(D) on nonempty opponent quitting coalitions D, with
the independent probabilities given by q. Let Q_i(q) be the corresponding
expected Z_i(D union{i}), including the empty opponent coalition. Continue
with tail w pays P_i(q)+H_i(q)w_i; forced Quit pays Q_i(q).

For a scheduled support S, set outside hazards zero and define

    z_i(q_S)=(Q_i(q)-P_i(q))/H_i(q), i in S.

This analytic map has z(0)=0 and Dz(0)=L_SS. The inverse function theorem
gives a local analytic q_S(w_S) with derivative L_SS^-1. Every scheduled
owner is exactly indifferent. Define Phi_S(w) by active outputs Q_i(q)
and quiet outputs P_i(q)+H_i(q)w_i. Then D Phi_S(0)=A_S. The quiet Nash
gap has derivative (A_S w)_i-J_iS L_SS^-1w_S, precisely the test in(F).
For pairs the exact inverse is q_j=w_i/(L_ij+w_i). For triples the actual
higher rewards enter the inverse map; none are discarded or sign-restricted.
They affect only Taylor remainders and the eventually chosen clock amplitude.

For the chosen word put F=Phi_Sm composed with ... composed with Phi_S1.
It is analytic near zero, fixes zero and has derivative H with the accepted
expanding eigenmode. The next lemma constructs genuine inverse iterates.

## 7. Signed inverse orbit and the complete-response telescope

Let F be C^2 near zero, F(0)=0, A=DF(0), and F(x)=A x+R(x). If
A V=rho V with rho>1 and V!=0, there is a
number rho<sigma<rho^2 and, for every sufficiently small a>0, an orbit

    F(w_n)=w_(n+1), n<0; w_n=a rho^n V+O(a^2 sigma^n), n<=0. (B)

For completeness choose sigma avoiding all eigenvalue moduli and split
real invariant spaces below and above sigma. Equivalent norms give
||A_s||<=alpha_s<sigma<alpha_f and ||A_f^-1||<=1/alpha_f. On sequences
n<=0 use ||x||_sigma=sup sigma^-n|x_n|. For forcing f_k, k<0, put

    (Gf)^s_n=sum_(k=-infinity)^(n-1) A_s^(n-1-k)f^s_k,
    (Gf)^f_n=-sum_(k=n)^(-1) A_f^(n-1-k)f^f_k.

The operator norm is at most1/(sigma-alpha_s)+1/(alpha_f-sigma), omitting
empty blocks, and (Gf)_(n+1)-A(Gf)_n=f_n. Set y_n=a rho^n V. Since
rho^(2n)<=sigma^n<=rho^n for n<=0, the map x->G(R(y+x)) sends a sufficiently
large ball ||x||_sigma<=C a^2 into itself and has Lipschitz constant O(a).
Banach contraction gives x and proves(B). No sign restriction is imposed.

Each actual hazard and quiet gap along(B) is its strictly positive linear
coefficient times a rho^n, plus O(a^2 sigma^n). Since(sigma/rho)^n<=1,
a sufficiently small fixed a makes every hazard proper and positive and
every quiet Nash gap positive, uniformly over all n<=0.

Play chronological blocks n=-1,-2,..., each in reverse support order
Sm,...,S1. Block n has tail w_n and output w_(n+1); the initial output is
w_0. At every date Continue equals its stated value, scheduled Quit ties,
and quiet Quit lies below. Unroll to any finite deadline and let the tail
remainder tend to zero. Its absolute value is bounded by the vanishing
state norm, because the corresponding survival coefficient is at most one.
Every scheduled deadline and the unilateral Never reply therefore pay w_0;
every other finite deadline pays at most w_0. Every complete randomized
reply averages these pure replies. Prescribed play averages its scheduled
deadlines and Never, proving U=B=e=w_0 exactly.

The hazards have finite positive total geometric sums. Every owner occurs,
so each original marginal Never mass is strictly between zero and one.
These are actual independent laws on natural dates, with no action after
an infinite prefix. The joint Never mass lies in(0,1), proving the theorem.

## 8. Tied first hits: continuous support selection

### 8.1. Data at a tied hit

Use architecture(A): Gamma_kl,Gamma_lk<0, Gamma_pj<0<Gamma_jp, and
Gamma_kj,Gamma_lj>0. Suppose both Gamma_kp,Gamma_lp<0 and

    alpha=-1/Gamma_pj,
    beta=-alpha Gamma_kj/Gamma_kp=-alpha Gamma_lj/Gamma_lp>0.

The first solo j sends e_p to w=e_p+alpha Gamma[:,j], and solo p of
duration beta sends w to z=beta Gamma_jp e_j. For T=I minus{p}, put
u=M_Tp/M_pp>0. The final triple hazards are t=beta u-alpha e_j>0, since

    t_j=-beta Gamma_kl u_l/Gamma_kj>0.

Thus the limiting return is rho e_p with rho=1+beta/M_pp>1. Every final
triple hazard, the main solo hazards, the first phase's two quiet gaps,
the middle phase's j gap, and the final p gap are strictly positive.

Row p has both signs and Gamma_pj<0, so at least one of Gamma_pk,Gamma_pl
is positive. Relabel k,l so Gamma_pl>0. The other sign is arbitrary.
Let U={p,k,l}; det Gamma_UU>0 by the positive-inverse diagonal identity.

### 8.2. The exact middle support selector

Fix a sufficiently small strictly negative participant matrix J and put
L=J-Gamma. The exact first root uses pair{p,j}. Its output v has

    v_p=J_pj q_j<0,
    v_k/x near alpha Gamma_kj>0,
    v_l/x near alpha Gamma_lj>0,

where x is the incoming p coordinate. The relevant exact indifference map
is z_i(q)=(Q_i(q)-P_i(q))/H_i(q). It does not depend on owner i's own
hazard. All outside-U hazards are zero for this middle root.

Treat the optional k hazard as t>=0. Solve the two equations

    z_p(t,q_l)=v_p, z_l(q_p,t)=v_l

for q_l=psi(t) and q_p=chi(t). Their derivatives at zero are L_pl<0 and
L_lp>0, respectively, so the solutions are analytic near zero. At t=0,

    psi(0)=v_p/(L_pl+v_p)>0,
    chi(0)=v_l/(L_lp+v_l)>0.

Define the divided quiet-k gap

    g(t)=v_k-z_k(chi(t),psi(t)).

The actual quiet-k gap is H_k g(t), so it has the same sign. At the
limiting origin J=0,

    psi'=-Gamma_pk/Gamma_pl,
    chi'=-Gamma_lk/Gamma_lp,
    g'=-det Gamma_UU/(Gamma_pl Gamma_lp)>0.                  (D)

These derivative signs persist for small J and small hazards. Inputs within
relative distance delta of the tied ray have |g(0)|<=C(delta+|J|+x)x.
Consequently any required zero of g is within C'(delta+|J|+x)x of zero,
and chi stays near beta x>0 when delta and the parameter neighborhood are
small. These are ordinary uniform IFT estimates on the scaled equations.

If Gamma_pk<0, then psi'>0. Choose t=0 when g(0)>=0; otherwise choose
the unique small positive root g(t)=0. Then q_l>0 and q_p>0, while q_k=t
is nonnegative. If t=0, k is quiet with a nonnegative gap. If t>0 all
three active owners are exactly indifferent. This selection is continuous.

If Gamma_pk>0, then psi'<0. The first endpoint psi(t_max)=0 occurs at

    t_max=v_p/(L_pk+v_p)>0.

Use t=0 if g(0)>=0. If g(0)<0<=g(t_max), use the unique root g(t)=0
between the endpoints. If g(t_max)<0, instead use the pair{p,k}:
q_k=t_max,q_l=0, and solve z_k(q_p,0)=v_k for q_p. The latter q_p is
strictly smaller than chi(t_max), because z_k is increasing in q_p and
v_k<z_k(chi(t_max),0). Since z_l is also increasing in q_p, this new
choice has z_l(q_p,t_max)<v_l: quiet l has a positive gap. Its q_p remains
near beta x>0. At either switching boundary the adjacent formulas agree,
so this selection is continuous as well.

Thus the middle root is selected continuously among supports{p,l},
{p,k,l},{p,k}. It always has q_p>0, nonnegative weak hazards, exact active
indifferences and nonnegative quiet gaps. The remaining quiet owner j has
a strictly positive gap by its limiting margin beta Gamma_jp. Endpoints
are included; no division by a weak hazard or strict quiet margin occurs.

### 8.3. An invariant cone for the actual return

Fix delta>0 small and set

    K_delta={w: w_p=x>=0, -delta x<=w_i<=0 for i!=p}.

Apply the first exact pair root, then the middle selector above, then the
exact final triple T. Call the continuous return F; F(0)=0. Every root is
an actual Nash root against its actual tail. The first pair hazard of p
may vanish on w_j=0; it is nonnegative because

    q_p=w_j/(L_jp+w_j), L_jp<0.

The first j hazard is strictly positive. The first quiet gaps and the final
triple hazards and quiet p gap remain strictly positive throughout a small
relative cone. The middle selector supplies its only potentially vanishing
quiet gap. Every owner acts positively in at least one phase: p in the
middle and j,k,l in the final triple.

At J=0 and x=0, the scaled return at direction e_p is rho e_p with rho>1.
The partial inverses and the finite piecewise middle selector are continuous
in the scaled variables(w/x,J,x), including their switching boundaries.
At x=0 all scaled equations use only Gamma,J, so delta and eta are first
chosen from Gamma alone. For each fixed J and higher completion, compactness
of the direction slice then permits an amplitude radius such that

    c x<=F_p(w)<=C x, with fixed C>=c>1,
    |F_i(w)|<=delta x/2 for i!=p.                            (E)

Here the second bound follows from the final triple: its active output
coordinates are Q_i(q_T)=sum_(m in T)J_im q_m+O(|q_T|^2). Its hazards are
between fixed positive multiples of x. For each fixed strictly negative J,
reduce the amplitude radius until the negative linear sum dominates the
quadratic remainder in every active row. Then F_i(w)<0 for every i!=p and
x>0. The same estimates ensure |F_i(w)|<=delta F_p(w), so

    F(K_delta intersect{x<=a0}) subset K_delta.

The eta bound depends only on Gamma. The amplitude a0 may depend on J and
all the finite higher rewards, exactly as allowed in the box theorem.

### 8.4. Cone compactness produces the entire inverse orbit

The following lemma needs only continuity. Suppose F is defined on a
truncated closed cone K as above, maps into the same untruncated cone,
fixes zero, and satisfies(E) with c>1. For every sufficiently small a>0 there is a sequence

    F(w_n)=w_(n+1), n<0; (w_0)_p=a;
    0<(w_n)_p<=a c^n, n<=0.                                (O)

Choose a strictly below the amplitude radius. For each N consider the
parameters t in[0,a] for which iterates0 through N of t e_p all lie in
the cone slice x<=a. This set is compact, inductively by continuity, and
contains an interval[0,b] with b>0. Its component containing zero has a
positive right endpoint t_N<=a c^(-N)<a. If all iterates were strictly
below a there, continuity would extend that component, since F is defined
on a larger slice. Thus an iterate reaches a. It must be the Nth: any
earlier hit would be followed by a value above a, by the expansion bound.

Set w_n^(N)=F^(N+n)(t_N e_p), -N<=n<=0. Their p coordinates lie between
a C^n and a c^n. For each fixed n the cone slice is compact. A diagonal
subsequence gives w_n for every n<=0, with the same bounds. Continuity
gives F(w_n)=w_(n+1), proving(O). In particular the orbit tends to zero
geometrically and its initial point is nonzero. This is an actual sequence
of chronological tails, not a limiting unconnected root correspondence.

Use these roots in chronological blocks n=-1,-2,..., each in reverse
construction order. Every Continue equals its assigned value, every
positive-hazard Quit ties it, and every quiet Quit lies below or ties it.
The vanishing-tail complete-response telescope proves U=B=e exactly.
All hazards are O((w_n)_p), hence summable; each owner has positive hazards
in every block. The original marginal Never masses therefore all lie in
(0,1). This supplies the same actual Nash conclusion at tied first hits.


## Source adapter and remaining boundary

For an actual Fin4 counterexample, `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
and `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean` supply
single-pivot native absorbing-gap data after subtracting the pivot's own
singleton level from its recipient rewards on nonempty coalitions.
Finite deadlines dominate Never at nonnegative own singleton, using
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.
This preserves debt on absorbing profiles: prescribed and finite-deadline
payoffs lose the same pivot constant, and the late-deadline limit still
dominates the shifted Never payoff. If A>0 is the native absorbing debt
infimum and M0>=1 bounds rewards, move the smallest original Never mass
to a finite date. Its size is at most nu^(1/4). Coupling the moved law changes
four prescribed payoffs and three other-owner reply caps by at most twice
M0 times that mass each; its own cap is unchanged. The new profile absorbs,
giving A<=D+14 M0 nu^(1/4), also on the compact carrier by closure.
Thus its global least original Never obeys mu>0; the theorem adds mu<1
whenever the native pair data satisfy its assumptions.

The complete cap recursion is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
The argument here supplies the actual roots and infinite limit, rather
than assuming the recursion's continuation inputs. It excludes the global
AllNever endpoint for a general open family of singleton and participant
data, with arbitrary higher completions, including tied first hits. It does
not close the positive global-minimum branch. Zero singleton comparisons,
inverse-positivity boundaries and arbitrary participant matrices remain
outside the stated hypotheses.

## Exact separating table and implementation overlap

The two-triple branch is needed beyond the earlier two-pair and
pair/pair/triple tests. Consider

    Gamma=[0,-14,-3,25; -10,0,15,-16; -30,30,0,17; 24,3,-13,0],
    J_ij=-1/1000000 for i!=j.

The matrix has determinant133220, strictly positive inverse, and no
complementary-minor ties. Take(p,j,k,l)=(1,3,0,2). The constructed word is
13,012,023. At J=0, its expanding eigenvalue is2010815/818496>1;
all hazards except the first pair's owner1 are positive. At the displayed J,
the exact checker below certifies all twelve strict tests. It also rejects
every partition into two pairs and all24 relabelings of the pair/pair/triple
word in Section4, by exhausting every real expanding eigenspace. Cyclic
rotation of a word transfers an accepted mode to an accepted mode, scaling
some phase tests by positive rho; it adds no missing order.

Every Gamma-tJ, 0<=t<=1, nevertheless passes the whole-pencil screen: it is
R0, degree1 and standard Q. Here R0 excludes any nonzero x>=0 with Mx>=0
and x_i(Mx)_i=0. In this paragraph M denotes a pencil matrix. The checked
principal inverse-norm bounds exclude kernels on supports of sizes2,3,4;
a negative entry in every column excludes singleton supports. For Gamma
at offset-minus-ones, any complementary root x has Gamma x>=ones, hence
x>=Gamma^-1 ones>>0. It must be the unique full-support root, with positive
index detGamma. The nonvanishing of min(x,Mx) on the unit sphere is uniform
over the compact pencil, so degree1 persists. Standard Q means that every
offset b admits x>=0 with Mx+b>=0 and x_i(Mx+b)_i=0; bounded-offset homotopy
on a sufficiently large sphere gives this property. The checker also verifies
the generic cross ratios, principal J determinants and determinant resultants.

No proper literal response-invariant quotient explains this example, even
after positive recipient scaling. The necessary condition
`quittingSingletonBlockRowSum_eq_of_responseInvariant` and the sum identity
`sum_quittingSingletonBlockRowSum_eq_totalRowSum` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
require equal scaled singleton row sums into each block. Total row sums
are(8,-11,17,14), so owner1 must be a singleton. Blocks23 and023 have
internal sums of opposite signs: (17,-13) and(22,-13,11). For blocks02
and03, the internal/total ratios are respectively(-3/8,-30/17) and
(25/8,12/7), which are unequal. These exhaust all possible merges.
The singleton comparison matrix subtracts the recipient's own singleton,
so the obstruction survives the native pivot-row subtraction.

The implemented `InverseRawSource` in
`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`
requires nonnegative scheduled native participant rewards, together with
higher-reward caps. Its participant condition fails here under every
labeling. This is a focused separation of source producers; individual
higher completions may still satisfy other UE theorems. The new contribution
is automatic support selection over the stated singleton region and a
uniform negative participant box. The signed local inverse construction is
reused. No strategic input remains unproduced.

The tied-hit cases are nonempty. With(p,j,k,l)=(0,1,2,3), both matrices

    G_minus=[0,-6,-10,30; 11,0,20,-27; -12,11,0,-26; -12,11,-25,0],
    G_plus =[0,-6,20,4; 16,0,-3,-9; -9,9,0,-1; -9,9,-30,0]

have positive determinant and strictly positive inverse. Their first-hit
ratios tie exactly. The first has Gamma_pk<0; the second has both
Gamma_pk,Gamma_pl>0 and exercises the endpoint branch of the selector.
Section8 constructs actual clocks at these matrices; approximation by
untied matrices is not being used.

The following standalone Python3/SymPy program uses exact arithmetic and
polynomial root isolation. It is a finite separation certificate; the
general theorem is proved above.

```python
import itertools
import sympy as s
I=tuple(range(4)); x,t=s.symbols('x t')
G=s.Matrix([[0,-14,-3,25],[-10,0,15,-16],[-30,30,0,17],[24,3,-13,0]])
J=-(s.ones(4)-s.eye(4))/10**6
assert G.det()>0 and all(v>0 for v in G.inv())
assert all(G[k,j]*G[l,p]!=G[l,j]*G[k,p] for p,j,k,l in itertools.permutations(I))
assert [(i,j) for i,j in itertools.combinations(I,2) if G[i,j]<0 and G[j,i]<0]==[(0,1),(0,2)]
def phase(S):
 C=(J-G).extract(S,S).inv(); A=s.eye(4)
 for i in I:
  if i in S:
   for j in I:A[i,j]=0
   row=J.extract([i],S)*C
  else:row=G.extract([i],S)*C
  for j,v in zip(S,row):A[i,j]=v
 return A,C
def data(word):
 H=s.eye(4)
 for S in word:H=phase(S)[0]*H
 f=s.Poly(H.charpoly(x).as_expr(),x)
 assert s.gcd(f.as_expr(),s.diff(f.as_expr(),x))==1
 assert f.eval(1)!=0
 intervals=[(a,b) for (a,b),m in f.intervals(eps=s.Rational(1,10**12)) if a>1 and m==1]
 assert f.count_roots(1,s.oo)==len(intervals)
 return H,intervals
def signs(word,H,a,b,column=0):
 V=(x*s.eye(4)-H).adjugate()[:,column]; W=V; vals=[]
 for S in word:
  A,C=phase(S); h=C*W.extract(S,[0]); U=A*W
  vals+=list(h)+[U[i]-(J.extract([i],S)*h)[0] for i in I if i not in S]
  W=U
 out=[]
 for v in vals:
  v=s.factor(v)
  if v==0:out.append(0);continue
  assert s.Poly(v,x).count_roots(a,b)==0
  out.append(int(s.sign(v.subs(x,(a+b)/2))))
 assert any(out)
 return out
word=[(1,3),(0,1,2),(0,2,3)];H,intervals=data(word)
assert len(intervals)==1
a,b=intervals[0];sg=signs(word,H,a,b,1)
assert all(v>0 for v in sg) or all(v<0 for v in sg)
print('PASS pair-triple-triple: all12 strict tests throughout exact isolating interval',a,b)
for S in ((0,1),(0,2),(0,3)):
 word=[S,tuple(i for i in I if i not in S)];H,intervals=data(word)
 for a,b in intervals:
  sg=signs(word,H,a,b)
  assert 1 in sg and -1 in sg
print('PASS: every two-pair test rejected')
for p,j,k,l in itertools.permutations(I):
 word=[tuple(sorted((p,j))),tuple(sorted((p,k))),tuple(i for i in I if i!=p)]
 H,intervals=data(word)
 for a,b in intervals:
  sg=signs(word,H,a,b,p)
  assert 1 in sg and -1 in sg
print('PASS: all24 previous pair-pair-triple relabelings rejected')
norm=lambda A:max(sum(abs(A[i,j]) for j in range(A.cols)) for i in range(A.rows))
for n in (2,3,4):
 for S in itertools.combinations(I,n):
  A=G.extract(S,S);C=J.extract(S,S)
  assert A.det()!=0 and norm(A.inv())*norm(C)<1
assert all(any(G[i,j]<0 and abs(J[i,j])<-G[i,j] for i in I) for j in I)
# Thus every Gamma-tJ, 0<=t<=1, is R0. Positive inverse at t=0 makes
# LCP(Gamma,-ones) have its unique root Gamma^-1 ones>0, index +1.
# R0 degree homotopy gives degree1, hence standard Q, along the pencil.
full=(G-t*J).det()
assert all(G[i,j]*J[j,i]-G[j,i]*J[i,j]!=0 for i,j in itertools.combinations(I,2))
assert J.det()!=0
for S in itertools.combinations(I,3):
 assert J.extract(S,S).det()!=0
 assert s.resultant((G-t*J).extract(S,S).det(),full,t)!=0
print('PASS: whole pencil R0, degree1/Q, and generic cross/principal/resultant conditions')

assert list(G*s.ones(4,1))==[8,-11,17,14]
assert list(G.extract([0,2,3],[0,2,3])*s.ones(3,1))==[22,-13,11]
assert s.Rational(-3,8)!=s.Rational(-30,17) and s.Rational(25,8)!=s.Rational(12,7)
print('PASS no proper response quotient, even after positive recipient scaling')

for T in (s.Matrix([[0,-6,-10,30],[11,0,20,-27],[-12,11,0,-26],[-12,11,-25,0]]),
          s.Matrix([[0,-6,20,4],[16,0,-3,-9],[-9,9,0,-1],[-9,9,-30,0]])):
 assert T.det()>0 and all(v>0 for v in T.inv())
 assert T[2,3]<0 and T[3,2]<0 and T[0,1]<0<T[1,0]
 assert T[2,1]>0 and T[3,1]>0 and T[2,0]<0 and T[3,0]<0
 assert T[2,1]*T[3,0]==T[3,1]*T[2,0]
print('PASS exact tied-hit boundaries of both selector types')
```

## Lean handoff

Formalize the negative-edge graph lemma, the two support-selection branches,
and the strict negative-box continuation of their simple modes. Include
the continuous support selector and cone compactness argument for tied hits.
The active support maps and inverse-orbit constructions supply an actual
natural-date law. Reuse the complete-cap recursion and verify the vanishing
remainder for all finite replies and literal Never. The theorem inputs are
raw matrix hypotheses, not a supplied eigenmode, root sequence or tail.
The endpoint is U=B=e and0<nu<1, not an absorbing or original-game UE law.
