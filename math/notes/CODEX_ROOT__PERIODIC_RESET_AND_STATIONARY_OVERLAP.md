# A repeated negative-pair reset produces a uniform equilibrium

Owner: CODEX_ROOT. Independently reviewed ordinary mathematics, not Lean-checked. The finite raw
criterion below produces one fixed UE payoff without an actual continuation
starter or a positive-gap assumption. Additional reward-table coverage over
existing producers remains UNESTABLISHED, so this is not an export proposal.

The contracting pair algebra and rectangle guards are inherited from
[the two-zero reduction](../exports/TWO_ZERO_CONTINUATION_REDUCTIONS.md),
Section7. The new step is a finite periodic implementation: a numerical seam
is replaced by actual payoff and full-cap fixed points with explicit errors.

## 1. Raw criterion

Four distinct roles are p,i,j,k. Nonempty quitting coalition S pays finite
original reward R(S), and live/Never pay zero. Let kappa_l=R_l({l}) and
Z_l(S)=R_l(S)-kappa_l for nonempty S only. The kappa_l have arbitrary signs.
Write Gamma_lh=Z_l({h}) for l!=h and Gamma_ll=0. Require

    Gamma_ij=-a<0, Gamma_ji=-b<0,
    Pi=Z_i({i,j})>0, Pj=Z_j({i,j})>0,
    A=Gamma_ip>0, B=Gamma_jp>0.

Compute directly from the table

    c_i=B/b, c_j=A/a, C=c_i+c_j, W=1+C, D=1+Pi/a+Pj/b,
    g_l=Gamma_lp+c_i Gamma_li+c_j Gamma_lj,
    E_l=Z_l({i,j})+Gamma_li Pj/b+Gamma_lj Pi/a,
    K_l=c_i c_j E_l/D                              (l=p,k).

Require K_p!=0 and define

    t=-g_p/K_p in(0,1),
    beta=(g_k+tK_k)/(W+c_i c_j t)>0,
    S=1/[(1+c_i t)(1+c_j t)],
    E_k^entry=(1-t)beta+t Gamma_kp>=0.                 (1)

Set v_p=v_i=v_j=0,v_k=beta and x0=tA,y0=tB,A0=a+Pi,B0=b+Pj. For l=p,k let

    G_l(x,y)=v_l(A0+x)(B0+y)
       +(v_l-Gamma_lj)(Pi/a)x(B0+y)
       +(v_l-Gamma_li)(Pj/b)y(A0+x)
       +(v_l-E_l/D)(Pi Pj/(ab))xy
       -Z_l({l,i})A0 y-Z_l({l,j})B0 x-Z_l({l,i,j})xy.     (2)

Require G_l>=0 at all four corners of [0,x0] x [0,y0], for BOTH l=p,k.
These eight arithmetic tests include the structural identity G_p(0,0)=0.
The participant rewards Z_i({i,p}), Z_j({j,p}), Z_k({k,p}) are unrestricted.
No strategy, actual continuation, inverse column, or compact source is assumed.

**Theorem.** Every table passing these raw tests has the fixed uniform-
equilibrium payoff w_l=kappa_l+v_l. For each accuracy an actual finite-period
profile is produced; it controls every unilateral behavioral replacement at
all sufficiently long horizons. No new unrestricted Fin4 conclusion follows.

## 2. Actual finite periods and exact numerical annotations

For n>=1 recursively define

    q_(n,j)=x_(n-1)/(a+Pi+x_(n-1)), x_n=Pi q_(n,j),
    q_(n,i)=y_(n-1)/(b+Pj+y_(n-1)), y_n=Pj q_(n,i),
    q_(n,p)=q_(n,k)=0.

For m>=1 put h=1-(1-t)^(1/m). Repeat the FINITE chronological word

    q_n,q_(n-1),...,q_1, then m solo-p roots of hazard h.       (3)

All scheduled hazards are proper and positive. The vector v is only a
numerical seam annotation, never an assumed actual tail or an infinite phase.
The finite pair survival factors telescope to

    m_j,n=(a+x_n)/(a+x0), m_i,n=(b+y_n)/(b+y0),
    c_n=(1-t)m_i,n m_j,n<=1-t<1.                           (4)

Put eta=min(t,1-(1-q_(1,i))(1-q_(1,j)))>0. Every deleted-player opponent
family has period survival H_l,n<=1-eta: p's opponents include the first
pair root, i/j's opponents include the solo-p block, and k's opponents
include all scheduled owners. This holds uniformly in n,m.

The finite word's prescribed affine payoff map applied to v gives v_n.
The solo block output is exactly T=(0,x0,y0,E_k^entry) in roles p,i,j,k,
independent of m. At each pair root the exact active equalities are

    -a q_(n,j)+(1-q_(n,j))x_(n-1)=Pi q_(n,j)=x_n,
    -b q_(n,i)+(1-q_(n,i))y_(n-1)=Pj q_(n,i)=y_n.

For l=p,k the passive annotation is

    v_l,n=v_l+(v_l-Gamma_lj)x_n/a+(v_l-Gamma_li)y_n/b
                   +(v_l-E_l/D)x_n y_n/(ab).              (5)

At n=0 this equals T_l because g_p+tK_p=0 and the beta identity in(1).
Substitution in the passive affine root recursion proves(5) by induction;
the coefficient identity is D=1+Pi/a+Pj/b. These are numerical finite-root
identities and require no realization of the seam. Thus v_n has active
coordinates x_n,y_n and passive coordinates(5), for EVERY finite m.

Set e_n=max_l|v_l,n-v_l|. It is explicitly computable and tends to0
geometrically, since x_n<=x0[Pi/(a+Pi)]^n and similarly for y_n.

## 3. Full finite-word cap bound

For a fixed finite word, the complete response map at scalar tail value z is

    F_l(z)=max(D_l,P_l+H_l,n z),                            (6)

where D_l is the maximum of all head deadline rewards and P_l the passive
head reward. This max-affine numerical map has Lipschitz constant H_l,n.
It is meaningful even when z is only an annotation. We prove

    F_l(v_l)<=v_l,n+M h, M=max(1,max|Z_l(S)|).              (7)

A quiet owner's deadline at solo-block position d, 0<=d<m, earns exactly

    Gamma_lp[1-(1-h)^d]+(1-h)^d h Z_l({l,p}).               (8)

It is at most max(0,t Gamma_lp)+M h. For i,j the reference T_l=t Gamma_lp
is positive. For k, (1) and beta>0 give T_k>=max(0,t Gamma_kp). Every tail
deadline is priced by T_l. The pivot's solo-block cap at its zero seam is0.
Hence this block's full cap is at most T+M h.

For each quiet pair row, multiplying v_l,n-Q_l(q_n) by the positive
(a+Pi+x)(b+Pj+y), with x=x_(n-1),y=y_(n-1), gives exactly G_l(x,y).
The current point lies in the tested rectangle, and a bilinear polynomial
is a convex combination of its corner values. Thus all quiet pair offers
are at most their annotations; the active offers are equalities. The literal
root max-cap recursion propagates an inherited error M h with coefficient
at most one. It does not add M h at each date. Induction proves(7) for every
head deadline and the through-tail option of the whole finite word.

## 4. Actual periodic fixed points

The actual prescribed periodic payoff u_n is the affine payoff fixed point,
so (4) and the exact annotated output give

    u_l,n-v_l=(v_l,n-v_l)/(1-c_n),
    |u_l,n-v_l|<=e_n/t.                                  (9)

The actual unrestricted response cap B_l,n,m is the unique fixed point of(6).
Indeed a deterministic deadline either occurs in the first period, or waits
through that period and receives P_l+H_l,n times a later deadline reward.
Pure Never is the limit of those later offers because opponents-only
survival decays geometrically. Taking suprema gives(6)'s fixed-point equation;
private randomized behavioral replacements are mixtures of these deadlines
and Never. Consequently (7) and H_l,n<=1-eta imply

    B_l,n,m<=v_l+(e_n+M h)/eta.                           (10)

If B_l,n,m>v_l, subtract v_l and absorb the contraction term; otherwise the
upper bound is automatic. This bounds all complete deviations, not only
stationary replacements or period-aligned stopping rules.

For epsilon>0 choose the least n>=1 with e_n<=epsilon min(t,eta)/4.
The geometric convergence proves termination. Choose an integer m satisfying
m>=4Mt/[epsilon eta(1-t)]. Then h<=-log(1-t)/m<=t/[m(1-t)] gives
M h<=epsilon eta/4. Equations(9)-(10) put the native prescribed payoff within
epsilon/4 of v and every native deviation payoff at most v_l+epsilon/2.

## 5. Signed own levels and the uniform-horizon contract

Every opponent family absorbs almost surely, independently of the omitted
player's replacement. Thus ALL original terminal payoffs equal their native
payoffs plus kappa_l, including all deviations. This permits arbitrary signed
own levels without translating live or Never rewards. The fixed target is
w=kappa+v, independent of accuracy.

The produced period has length L=n+m. Opponents-only expected absorption time
is at most L/eta, uniformly over the omitted player's behavior. If M_R bounds
original absorbing rewards, terminal and T-stage average expected rewards
differ by at most M_R(L/eta+1)/T. The extra1 covers the selecting date's live
payoff convention. This bound is uniform over every behavioral replacement.
For all sufficiently large T it is below epsilon/4. Combining with(9)-(10),
and using a smaller internal accuracy if needed, proves delivery and deviation
bounds around ONE fixed target with ONE profile at every sufficiently long
horizon. No actual carrier starter was used at any point.

## 6. Coverage audit and limits

The [two-zero reduction](../exports/TWO_ZERO_CONTINUATION_REDUCTIONS.md)
already supplies the pair contraction and its corner comparisons. This note
uses them to build actual periodic approximate equilibria from a formal seam.
Its reward-table nonredundancy relative to prior UE producers remains open.

The [boundary inverse-column theorem](../exports/BOUNDARY_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM.md)
already supplies stationary equilibrium when a participant coalition reward
grows positively along a positive inverse column with other rewards bounded.
The hard singleton fixture is

    Gamma=[0,5,-1,-1; -2,0,1,1; 2,-1,0,-1; 2,-1,-1,0].

Every inverse column of this matrix is positive. Arbitrarily
large entry premiums therefore fall into known stationary regions. An exact
two-entry diagnostic gives the same warning: for the hard Gamma, setting
Z_2({0,2})=Z_3({0,3})=L and q=z/L yields limiting stationary equations

    (-5k+i+j,2p-i-j,(p+k+j)p-2p+k+j,(p+k+i)p-2p+k+i).

The positive root (1/4,1/10,1/4,1/4) has Jacobian determinant -15/2, so the
implicit-function theorem produces a stationary root for all large L with
other rewards fixed. This is a search diagnosis, not an additional export.

The large passive ray has an equally precise overlap. Hold all other entries
fixed and set Z_0({2,3})=L, Z_1({2,3})=rho L+K, with rho>-1/2 and K fixed.
For stationary hazards q=(a/L,0,b/L,c/L), put
F_l=(1-H_l)Q_l-P_l. The three active fields L F_l extend polynomially to
1/L=0, with limits

    (b+c-bc, c-2a, b-2a).

At (a,b,c)=(1,2,2) their Jacobian has determinant4. The implicit-function
theorem supplies a proper stationary active root for all large L. The quiet
row satisfies L F_1 -> -(2+4rho)<0, so Continue is optimal there as well.
Stationary active equalities and this quiet inequality price every deadline
and Never; each deleted-player opponent family absorbs geometrically.
Hence this is an exact stationary terminal Nash and a uniform target.

With pair participants Pi=Pj=1, the present reset criterion on this ray has
t=3/(L-2) and beta -> (2+4rho)/5. Thus its strict positive quiet-cap limit
is precisely the stationary quiet comparison. Increasing only these passive
rewards cannot establish new coverage of the periodic construction. This
argument gives no threshold at a specific finite L and does not prove the
whole raw criterion redundant.

The [signed passive-coalition theorem](../exports/SIGNED_PASSIVE_COALITION_REWARDS_UNIFORM_EQUILIBRIUM.md)
also supplies existing large-passive stationary regions. Their applicability
must be checked before claiming a new unbounded reward family here. The
400/-100/+1 fixture is already solved by absorbing Nash and is not a
separating example. No tested completion is presently certified outside all
relevant existing producers. Fin4 and unrestricted two-zero closure remain open.
