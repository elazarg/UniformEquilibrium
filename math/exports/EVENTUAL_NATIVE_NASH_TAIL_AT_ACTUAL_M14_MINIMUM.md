# Eventual full contact for an actual four-player observer minimum

## 1. Exact statement and scope

There are four players, indexed by 0,1,2,3. Native own-singleton and Never rewards are zero. Singleton passive rewards form the matrix

    Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0].

Every passive nonsingleton reward is zero. Every nonsingleton participant reward is -5 except the four successor-pair rewards 13 on the cycle 0->1->3->2->0. Thus the participant-pair matrix is

    J=[0,-5,13,-5; 13,0,-5,-5; -5,-5,0,13; -5,13,-5,0].

These rules specify every absorbing reward Z_i(D).

An actual profile consists of independent private stopping laws on the nonnegative integers and Never. The earliest finite date absorbs at its quitter coalition. Write U_i for prescribed expected payoff, B_i for the supremum over every unilateral private behavioral replacement, e_i for pure Never payoff, d_i=B_i-U_i, and nu for joint Never probability. A profile is **ALL-END** if B_i=e_i for every i, and **observer-exact** if d_i=0 for i in {0,1,3}.

**Theorem.** Fix r>=0. Suppose an actual profile is ALL-END and observer-exact, has strictly positive marginal Never probabilities, and minimizes

    J_r=d_2+r nu

over a carrier containing every actual independent observer-exact profile. If all four hazards are strictly positive at every sufficiently late physical date, then only finitely many dates have a strict pivot-2 preference for Never over immediate Quit. Every sufficiently late conditional whole tail consequently has zero debt for all four players: it is a native Nash tail with positive Never probability.

The theorem excludes the entire eventual-full-support mode with infinitely many strict pivot comparisons, including arbitrarily sparse strict dates. It leaves finite heads followed by fully contact tails, sparse owner supports, and inherited semantic points without an actual representative. It does not assert minimum attainment, actual realization, eventual full support, or a uniform equilibrium. In particular, positive Never mass remains; replacing absorbing rewards Z by 4+Z does not transport the native Nash conclusion to the shifted game.

The incoming actual profile and its minimum/support hypotheses are retained. Every additional object used to exclude the stated mode is produced below: exact finite variations, a finite constraint-qualification anchor, critical directions, compact multiplier sets, and a contradictory second variation. No continuation, rate, correction strategy, or multiplier bound is assumed as a strategic input.

## 2. Actual responses, finite splicing, and root coordinates

Let q_i be a root hazard, H_i(q)=prod_(j!=i)(1-q_j), H(q)=diag(H_i(q)), and c(q)=prod_i(1-q_i). With x_i=q_i/(1-q_i), the exact passive and Quit offers are

    P_i(q)=H_i(q) sum_j Gamma_ij x_j,
    Q_i(q)=-5[1-H_i(q)]+18H_i(q)x_pred(i),
    pred=(2,0,3,1).

These expressions are multilinear polynomials in q; their linear terms are Gamma q and Jq. The apparent odds denominators cancel. The literal Never recurrence is

    e_k=P(q_k)+H(q_k)e_(k+1).                       (1)

The conditional properties used here are inherited from the whole actual profile. Conditioning independent clocks on surviving a finite cut preserves independence and positive marginal Never mass. A conditional response exceeding conditional Never could be used after following Never to that cut; its improvement would be multiplied by positive opponent survival, contradicting whole ALL-END. A conditional observer debt could similarly improve that observer's prescribed head-and-tail law by positive joint survival, contradicting observer exactness. Thus every conditional whole tail is ALL-END and observer-exact.

At an active observer date, immediate Quit is a maximizer because every positive atom of an optimal prescribed stopping law is optimal. Hence, on a full-support tail,

    e_k-Q(q_k)=g_k e2,    g_k>=0.                   (2)

A date is strict when g_k>0 and tied when g_k=0. Observers are always in contact; at a tied date all four players are in contact.

A finite variation retaining (1)-(2), its literal continuation, and its entrance Never vector preserves all full caps. Backwards induction uses the maximum of immediate Quit and Continue carrying the full continuation cap. Never still attains that maximum; every observer's prescribed law is optimal. The unchanged head therefore sees exactly the same full caps and observer prescribed payoffs. If its joint survival is s>0, the change in the whole objective is s times the change in the conditional objective. All finite fixed-entrance variations below are consequently valid local comparisons at the given global minimum.

This includes arbitrary behavioral deviations. Along the unique live history, fixing a deviator's private random bits determines a finite quitting date or Never. Every such response is priced by the root maximum and the literal continuation cap; averaging cannot improve it. All prescribed root randomization is independent and private.

## 3. Exact energy and nonlinear storage

Put

    L=J-Gamma, det L=-12568,
    v=Gamma^-1 e2=(4,5,1,3)/11,
    w^T=1^T Gamma^-1=(7,10,13,8)/11,
    PD=(1/10)[-4,2,12,-2; 2,-8,8,8; 12,8,-35,19; -2,8,19,-17],
    PV=(1/100)[-183,60,141,97; 60,-49,137,-44;
                          141,137,-282,111; 97,-44,111,-93].

For symmetric P define

    calQ(P)=[P Gamma^-1 J+J^T Gamma^-T P-P]/2,
    K_jj=0, K_jk=(w_j J_jk+w_k J_kj-1)/2 for j!=k,
    QD=calQ(PD), QV=calQ(PV)-K.

Direct rational multiplication gives PD v=e2 and PV v=(13/11)e2. The leading principal minors are

    QD: 7,3951/100,290527/2000,15333879/40000;
    QV: 4397/200,1143956171/4840000,
         4506212701697/5324000000,
         905937923038697/1064800000000.

Thus QD and QV are positive definite. Fix r and set

    P_r=PD+rPV, R_r=QD+rQV,
    Phi(e)=e^T Gamma^-T P_r Gamma^-1 e/2.

For independent variables (e,q) near zero define T(e,q)=H(q)^-1[e-P(q)], and

    ell(e,q)=q_2[e_2-Q_2(q)]
               +r[c(q)-1+w^T e-c(q)w^T T(e,q)],
    M_r=e2 e2^T+r diag(w)-P_r Gamma^-1,
    sigma(e,q)=ell(e,q)-q^T M_r[e-Q(q)]
                                      -Phi(e)+c(q)Phi(T(e,q)).    (3)

The raw identities imply M_r e2=0, so the contact correction vanishes identically when (2) holds. The ambient quadratic expansion is

    sigma(e,q)=-q^T R_r q+R(e,q),
    R=O(|q|^3+|q|^2|e|+|q||e|^2).                 (4)

Here and below norms and constants are fixed finite-dimensional ones; constants may depend on the table and r. To verify (4), the quadratic part of ell is

    q^T[e2 e2^T+r diag(w)](e-Jq)+r q^T Kq.

The K term follows by expanding passive singleton offers and joint survival: the coefficient of q_j q_k in the r bracket, apart from diag(w)e, is -1 because every passive pair reward is zero and w^T Gamma=1^T. Subtracting the M_r correction leaves q^T P_r Gamma^-1(e-Jq)+r q^T Kq. The quadratic storage difference is

    Phi(e)-Phi(e-Gamma q)
        =q^T P_r Gamma^-1(e-Jq)+q^T calQ(P_r)q,

which proves (4). The remainder is analytic, vanishes at q=0 for every e, and obeys locally

    ||R_qq||+||R_qe||<=C(|q|+|e|),
    ||R_ee||<=C|q|.                                (5)

For an actual contact tail, the pivot debt has the exact recursion

    d_2,k=q_2,k g_k+c_k d_2,k+1.

Define

    j_k=d_2,k+r nu_k,
    V_k=j_k-r+r w^T e_k-Phi(e_k).

Then (1)-(3) give

    V_k=sigma(e_k,q_k)+c_k V_(k+1).                 (6)

For any finite window, with pi_k joint survival from its entrance to k,

    V_T=sum_(T<=k<N) pi_k sigma(e_k,q_k)+pi_N V_N.  (7)

This is an exact identity; V_N is fixed when the continuation is unchanged.

## 4. A fixed five-date exclusion and geometric tail decay

First, sufficiently late five-date full-support windows cannot have all five pivot comparisons strict. Retain the continuation, impose all 15 observer contacts, and fix all four entrance Never values. At zero hazards and zero continuation payoffs, write a_k for a signed hazard direction and f_k=sum_(m>=k)a_m. The 19 constraint rows are

    (J a_k-Gamma f_k)_i=0, i in {0,1,3}, k=0,...,4,
    Gamma f_0=0.

Order variables by date/player and rows by date/observer followed by entrance player. Omitting the last variable, player3 at date4, gives determinant77996937216. The kernel is spanned by

    (1045,775,970,1747),
    (-4674,-3575,-4373,-7445),
    (7829,6164,7351,11910),
    (-5820,-4708,-5464,-8476),
    (1620,1344,1516,2264).

The quadratic coefficient of

    e_2,0-u_2,0+r[c+w^T e_0-1]

where c is the whole window's joint Continue probability, is -sum a_k^T R_r a_k on this tangent. This follows from (3)-(4) and telescoping, since f_0=f_5=0. Its debt and survival coefficients are respectively

    -1157984156,  -5894461073/11.                   (8)

The augmented objective has zero ambient differential at zero data. The fixed nonzero minor gives a one-dimensional smooth exact constraint fiber near zero. At a constrained local minimum, the unique stationary multipliers converge to the zero-data multipliers: they solve a fixed invertible minor, and the contact multipliers there are zero after adding the entrance combination e_2,0+r w^T e_0. The constrained Hessian consequently remains negative on its nonzero tangent near zero, contradicting the second-order necessary condition. Strict pivot gaps and positive hazards make a sufficiently small two-sided part of the fiber feasible; their margins need no uniform lower bound.

Positive marginal Never masses imply that every remaining finite-clock mass tends to zero. Bounded rewards then make late prescribed and Never continuation payoffs tend to zero, while conditional joint Never mass tends to one. Thus every sufficiently late five-date window meets the small-data neighborhood just proved. By Section 2 its variation is an admissible whole-profile comparison. Every late strict run therefore has length at most four.

This also produces geometric decay. Let f_i,k be the remaining conditional finite mass of clock i, and m_k=sum_i f_i,k. Independence and bounded rewards give

    e_k=Gamma f_k+O(m_k^2).                         (9)

At a tied date all players are in contact, so e_k=Q(q_k)=Jq_k+O(m_k^2), using q_i,k<=f_i,k. Invert Gamma to obtain

    m_k<=C sum_i q_i,k+C m_k^2.

Hence sum_i q_i,k>=c m_k late. The exact clock identity is

    m_k-m_(k+1)=sum_i q_i,k(1-f_i,k+1).

At a tied date this gives m_(k+1)<=(1-c')m_k for some c'>0. The masses are nonincreasing elsewhere, and a tied date occurs in every five-date block. Therefore

    m_(k+5)<=(1-c')m_k,  m_k=O(rho^k), rho<1.       (10)

The total remaining hazard eta_k is at most sum_i[-log(1-f_i,k)]<=2m_k late. States, hazards, and gaps thus tend to zero geometrically. No tail-rate assumption has been added.

## 5. Backward controls and uniform curvature

Near zero solve

    Q(q)-P(q)-H(q)t+g e2=0

for q=Psi(t,g). The derivative in q is L, so the analytic implicit function theorem gives one signed neighborhood and an analytic map. Define F(t,g)=Q(Psi(t,g))+g e2. Then

    e_k=F(e_(k+1),g_k), q_k=Psi(e_(k+1),g_k),
    Psi_t(0)=L^-1, Psi_g(0)=-L^-1e2,
    M:=F_t(0)=J L^-1,
    h:=F_g(0)=-Gamma L^-1e2.                        (11)

All first and second derivatives are bounded on a smaller neighborhood. Take the starting cutoff sufficiently late that the chart is valid at every later date and every matrix M_k=F_t(e_(k+1),g_k) is invertible. Equation (10) gives

    M_k=M+O(rho^k), h_k:=F_g(e_(k+1),g_k)=h+O(rho^k).

The signed chart is used only analytically. At the actual point, all finite-window hazards lie in (0,1); small finite perturbations with g>=0 remain actual and satisfy the response comparisons of Section 2.

We need curvature estimates independent of window length. Let E_k and a_k be state and hazard directions on a linearized feasible window [T,N), with E_T=E_N=0 and zero gap direction at every tied date. Differentiating (1) gives

    E_k=H(q_k)E_(k+1)+B_k a_k,
    B_k=DP(q_k)+DH(q_k)[.]e_(k+1).

At a tied date, E_k=DQ(q_k)a_k. If ||B_k||<=B and ||DQ(q_k)||<=C, a strict block of length at most l ending before a tied date j satisfies

    |E_k|<=C|a_j|+B sum_(v=k)^(j-1)|a_v|.

At j=N the first term is zero. Summing Cauchy-Schwarz bounds over disjoint blocks gives

    sum |E_k|^2
       <=[C^2(1+l(l+1))+B^2 l(l+1)] sum |a_k|^2.   (12)

Here l=4. Also gamma_k:=delta g_k=E_2,k-DQ_2(q_k)a_k, so

    sum(|E_(k+1)|^2+|gamma_k|^2)<=C_4 sum|a_k|^2.  (13)

The same undifferentiated argument gives

    sum |e_k|^2<=C_4[sum |q_k|^2+|e_N|^2],
    sum |e_k|<=C_4[sum |q_k|+|e_N|].

Boundary terms are retained; at a tied endpoint e_N=Q(q_N), they can instead be bounded using q_N. Thus ||e||_2+||q||_2<=C_4 eta_T on a late window.

The same first-order clock expansion as (9), using zero own-singleton rewards, gives U_i=e_i+O(m_k^2) and nu_k=1-m_k+O(m_k^2). Since w^T Gamma=1^T, it follows that

    V_k=O(eta_k^2).                                (14)

We next bound the full weighted Hessian of (7), not just its individual stages. On an affine hazard direction a, the linearized Never recurrence implies

    Gamma a_k=E_k-E_(k+1)+r_k,
    |r_k|<=C[(|q_k|+|e_(k+1)|)|a_k|+|q_k||E_(k+1)|].

Using E_T=0, w^T Gamma=1^T, and (12), the exact product derivative gives

    pi'_k/pi_k=w^T E_k+O(eta_T||a||_2),
    pi''_k/pi_k=(pi'_k/pi_k)^2
                            -sum_(T<=v<k,i)a_iv^2/(1-q_iv)^2,
    |pi''_k|<=C_4(|E_k|^2+||a||_2^2).              (15)

Equations (4)-(5) give

    |sigma_k|<=C(|q_k|^2+|q_k||e_k|^2),
    |sigma'_k|<=C[(|q_k|+|e_k|^2)|a_k|
                       +|q_k|(|q_k|+|e_k|)|E_k|].

Therefore the sums of |2pi'_k sigma'_k| and |pi''_k sigma_k| are at most C_4 eta_T||a||_2^2 and C_4 eta_T^2||a||_2^2, respectively. The fixed terminal term pi_N V_N has the latter bound by (14)-(15). The remainder Hessian in (5) is at most C_4 eta_T||a||_2^2 by (12). Since pi_k>=1-C eta_T, the ambient Hessian of (7) is bounded by

    -2lambda_min(R_r)sum pi_k|a_k|^2
                                  +C_4 eta_T sum|a_k|^2.        (16)

The independent state/control variables are (e_(k+1),g_k). Pullback through (Psi,F) must also be included. Set

    s(t,g)=sigma(F(t,g),Psi(t,g)), c(t,g)=c(Psi(t,g)).

On the chart the correction in (3) vanishes and T(F(t,g),Psi(t,g))=t, so (6) is exactly V_k=s_k+c_k V_(k+1). At the actual base the ambient local gradients in (7) are

    partial_(q_k)=pi_k[sigma_q(k)+c_q(k)V_(k+1)],
    partial_(e_k)=pi_k sigma_e(k).

Their sizes are O(pi_k eta_T) and O(pi_k eta_T^2). Bounded second derivatives of Psi,F and (13) therefore bound the pullback-curvature contribution by C_4 eta_T sum|a_k|^2.

For normal multipliers mu_k of F(e_(k+1),g_k)-e_k, the remaining curvature is

    sum mu_k^T D^2F[(E_(k+1),gamma_k),(E_(k+1),gamma_k)].

Its absolute value is at most C_4 sup|mu_k/pi_k| sum|a_k|^2. Combining this with (16) proves, for one kappa>0,

    Hess(Lagrangian)[direction,direction]
      <=[-kappa+C_4(eta_T+sup_(T<=k<N)|mu_k/pi_k|)]
                                                   sum|a_k|^2. (17)

All constants are independent of window length, strict-date spacing, endpoint conditioning, and strict margins. When pi is measured from an earlier fixed origin, divide the objective and multipliers by pi_T. Its positive limiting Never product bounds that normalization uniformly. Hence mu_k->0 uniformly on late tails suffices in (17).

## 6. Adjoint sign and decay

The exact normal adjoint for the recursion V_k=s_k+c_kV_(k+1) is

    mu_(k+1)=M_k^T mu_k+pi_k l_t,k,
    switch_k=h_k^T mu_k+pi_k l_g,k,
    l_t,k=s_t(k)+c_t(k)V_(k+1),
    l_g,k=s_g(k)+c_g(k)V_(k+1).                     (18)

The continuation value in these derivatives retains every discount derivative. Analyticity, (4), and (14) give l_t,k,l_g,k=O(m_k)=O(rho^k). At a minimum switch is nonnegative at tied controls g_k=0 and zero at strict controls g_k>0. For an abnormal multiplier, the forcing terms have objective coefficient zero.

We prove the needed asymptotic statement explicitly. Let B be real, invertible and diagonalizable, with two positive real eigenvalues lambda1>lambda2 and one nonreal conjugate pair of modulus b, where

    lambda1>1>lambda2>b>0.

Let ell observe every eigenspace, and let B_n=B+O(rho^n), ell_n=ell+O(rho^n), rho<1. Then:

- A nonzero homogeneous solution z_(n+1)=B_n z_n cannot have ell_n z_n eventually of one sign and zero at infinitely many dates.
- If z_(n+1)=B_n z_n+O(rho^n) and ell_n z_n+O(rho^n)=0 infinitely often, then z_n->0, uniformly for bounded initial data and common forcing bounds.

For an exact asymptotic conjugacy, write B_n=B+E_n and seek T_n=I+H_n with B_n T_n=T_(n+1)B. On matrix space let calL(H)=BHB^-1. Split its eigenmodes into moduli below one and moduli at least one. In an eigenbasis choose a norm with ||calL_stable||<=a<1 and ||calL_other^-1||<=1. Choose max(a,rho)<sigma0<1. The equation H_(n+1)=calL H_n+F_n has a bounded right inverse on the norm sup_(n>=N)sigma0^(-(n-N))|F_n|:

    H_n^stable=sum_(j=N)^(n-1)calL_stable^(n-1-j)F_j^stable,
    H_n^other=-sum_(j=n)^infinity calL_other^(n-1-j)F_j^other.

Its bounds are 1/(sigma0-a) and 1/(1-sigma0). The equation for the conjugacy is

    H_(n+1)=calL H_n+E_n B^-1+E_n H_n B^-1.

The fixed forcing and the operator multiplying H have norms O(rho^N). The displayed right inverse is therefore a contraction for large N, producing real T_n=I+O(sigma0^(n-N)), uniformly invertible and tending to I. Reality follows because the splitting and right inverse commute with conjugation. Every homogeneous solution has the exact form

    z_n=T_n B^(n-N)c.                              (19)

If c has a nonzero lambda1 component, the observed output has a fixed nonzero sign eventually. The same holds for a leading lambda2 component. If both vanish, the output is

    b^(n-N)[A cos((n-N)theta)+D sin((n-N)theta)+o(1)],

with A,D not both zero and 0<theta<pi. It takes both signs infinitely often with normalized magnitude bounded away from zero. Indeed the Cesaro means of cos(n theta+phi) and its square are 0 and 1/2. If its values were eventually at least -epsilon, the inequality x^2<=x+epsilon+epsilon^2 on [-epsilon,1] would contradict those means for small epsilon. Apply the same argument to its negative. This proves the homogeneous assertion without a Diophantine assumption.

For the forced recursion set y_n=T_n^-1 z_n. Then y_(n+1)=B y_n+O(rho^n). Its lambda1 coefficient is

    lambda1^(n-N)[y1_N+
          sum_(j=N)^(n-1)lambda1^(-(j+1-N))tilde u1_j].

The bracket converges. A nonzero limit gives an eventually nonzero output, contradicting infinitely many zeros. With zero limit, the coordinate equals the future sum

    -sum_(j=n)^infinity lambda1^(n-j-1)tilde u1_j=O(rho^n).

The stable coordinates are O(sigma^(n-N)) for every max(rho,lambda2)<sigma<1, including resonant cases. The geometric-series bounds are uniform over bounded initial/forcing families. This proves the second assertion.

For M14, put A=I-J^-1 Gamma and b0=J^-1e2. Equation (11) gives

    M=Gamma A^-1 Gamma^-1, h=-Gamma A^-1 b0.

The characteristic numerator of A is

    f(x)=13611x^4-54692x^3+81334x^2-52832x+12568,
    disc(f)=-2^11*17*397*2532437821<0.

Thus it has exactly two real roots and one conjugate pair. For p(z)=f(1-z),

    p(1/3)=-64/3, p(7/20)=107691/160000,
    p(-27/250)=81597451/3906250000,
    p(-107/1000)=-10810214789/10^12.

The real A roots are s in(13/20,2/3) and u in(1107/1000,277/250). The complex pair has real part (54692/13611-s-u)/2, exceeding 277/250 because

    (54692/13611-2/3-277/250)/2-277/250=31253/2268500>0.

Its modulus R therefore satisfies R>u>1>s>0. The spectrum of M^T has the required ordering 1/s>1>1/u>1/R. Finally,

    det A=12568/13611,
    det[b0,Ab0,A^2b0,A^3b0]=1043968/11440338672460347!=0.

So b0 is cyclic for A and A^-1; the similarity makes h cyclic for M, and h^T observes every M^T eigenspace. Apply the two asymptotic statements with B_n=M_n^T and ell_n=h_n^T.

## 7. A finite regular anchor from one-sided controls

Assume for contradiction that strict dates are infinite. Renumber a late cut satisfying all previous bounds, including invertibility of every M_k. For each N, freeze the literal continuation after N and use gamma=(g_0,...,g_(N-1)) as controls. Backwards recursion defines smooth entrance and objective maps calE_N(gamma)=e_0 and W_N(gamma)=V_0. The actual vector is a local minimum subject to

    calE_N(gamma)=e_0^*, gamma_k>=0.                (20)

Physical hazard bounds are inactive in a sufficiently small neighborhood of this finite actual vector.

For fixed m, variations of only the first m controls give exactly calE_m,W_m for every N>=m: later controls and the actual terminal state reproduce the unchanged actual continuation at m, including its objective value. Every derivative involving a fixed finite control set is thus literally independent of the later truncation. Write A_k=partial_(g_k)calE_N and b_k=partial_(g_k)W_N for N>k.

Failure of the Mangasarian-Fromovitz constraint qualification (MFCQ) in (20) is equivalent by finite-dimensional Farkas separation to a nonzero abnormal lambda with

    lambda^T A_k=0 at strict dates,
    lambda^T A_k>=0 at tied dates k<N.              (21)

There cannot be a separate nonzero inequality multiplier when lambda=0, since the coordinate inequality gradients are independent. The abnormal adjoint is

    z_0=lambda, z_(k+1)=M_k^T z_k,
    lambda^T A_k=h_k^T z_k.

If every N failed MFCQ, unit abnormal covectors would have a unit subsequential limit satisfying (21) at every date. The homogeneous result of Section 6 would force its tail solution to vanish. Every M_k is invertible, contradicting the nonzero initial covector. Therefore some finite N0 satisfies MFCQ. Every larger problem does too: an abnormal covector there would violate the already regular anchor.

Tied dates are essential here as one-sided controls. No spanning assumption about the sparse strict-date columns has been made.

## 8. Compact normal multipliers and the late contradiction

For N>=N0 let

    Lambda_N={lambda:
      b_k+lambda^T A_k=0 at strict k<N,
      b_k+lambda^T A_k>=0 at tied k<N}.

KKT under MFCQ makes these sets nonempty. They are closed, convex, and nested. Lambda_N0 is bounded: an unbounded multiplier sequence, divided by its norm, would yield a unit abnormal covector for the anchor. Hence

    Lambda_infinity=intersection_(N>=N0)Lambda_N

is nonempty and compact.

For each lambda in this intersection, the normal adjoint (18) starts at mu_0=lambda. Its forcing is O(rho^k), and its switching function vanishes at infinitely many strict dates. Section 6 gives mu_k->0 uniformly over this compact multiplier family. In particular,

    lim_(T->infinity)sup_(lambda in Lambda_infinity,k>=T)
                                         |mu_k(lambda)|=0.       (22)

Choose T so late that eta_T and (22) make the bracket in (17) negative for all these multipliers. Select any five strict dates after T, all before a finite M. The derivative map from these five controls to the four entrance coordinates at T has a nonzero kernel, regardless of its rank. Choose a nonzero kernel direction d.

Its state direction has E_T=E_M=0, is zero before T and after M, and has zero tied-control coordinates. Its hazard direction a is nonzero: otherwise (1) with terminal E_M=0 gives E=0, and gamma_k=E_2,k-DQ_2(q_k)a_k gives d=0. The direction is critical for every problem N>=max(M,N0), because normal stationarity is equality on its five strict coordinates and d calE_N=0, hence dW_N=0.

The directional second-order necessary condition under MFCQ provides, for each such N, a normal multiplier lambda_N in Lambda_N satisfying

    d^T D^2[W_N+lambda_N^T calE_N]d>=0.             (23)

It supplies an appropriate multiplier for each direction, not this inequality for every multiplier. To see the condition directly, consider second-order corrections v satisfying the linearized equalities with right side -D^2 calE_N[d,d] and nonnegative corrections in active coordinate inequalities where d_k=0. MFCQ gives strict feasibility of those corrections. If all normal multipliers gave negative quadratic forms, finite-dimensional linear-programming duality would give a strict objective-decreasing correction. The equality IFT and a strict MFCQ correction realize it by a feasible C2 arc, contradicting local minimality. Compactness of the multiplier set makes the dual maximum attainable.

Pass to a subsequence lambda_N->lambda_infinity in the compact anchor set. Nestedness puts its limit in Lambda_infinity. The direction has fixed finite support, so all first and second derivatives in (23) are independent of N once N>=M. Consequently

    d^T D^2[W_M+lambda_infinity^T calE_M]d>=0.

This is the dynamic Lagrangian form with adjoint (18) on the induced finite state/control direction. Equations (17), (22), and the choice of T make it strictly negative. The contradiction proves that strict dates are finite.

After their last occurrence, d_2,k=c_k d_2,k+1. Remaining finite-clock mass tends to zero, so bounded rewards give d_2,k+1->0. Iteration proves d_2,k=0 on every sufficiently late whole tail. Observer debts were already zero, which proves the native Nash-tail conclusion.

## 9. Boundary tests and actual-source consumer

The explicit energy minors, five-date Jacobian determinant and signed tangent in Sections 3-4 are finite rational positive tests. The adjoint argument uses exact spectral brackets and a nonzero cyclic determinant, rather than numerical eigenvalues.

An all-tied tail has no infinitely many positive controls, so the abnormal-covector contradiction does not apply. A finite set of strict dates is also retained. Sparse owner supports are excluded from the hypotheses because a zero hazard destroys the open finite control chart needed for the two-sided strict variations. No strict date is replaced by a tied equality during normality: tied gaps allow one-sided increases there, while the final critical direction has zero first derivative at all tied dates. The exact constraint qualification anchor is profile-dependent and fixed before the later critical direction is selected.

The theorem's adapter starts from an actual minimum satisfying the stated support hypothesis. It extracts literal hazards, uses the inherited conditional caps of Section 2, and derives the finite-contact rate from Section 4. All finite variations remain on the same observer-optimal carrier and preserve entrance full caps; the positive head survival turns their descent into a contradiction at the original profile. This is a residual-source consumer. It does not produce an actual representative of a compact semantic minimum or a support classification for that representative.

The operational correspondences are `quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff` and `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue` in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`. Conversely, `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile` in that file give the actual independent conditional-hazard implementation. The full cap recursion is `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`; `quittingTerminalSemanticPair_rootThenContinuation` in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` identifies literal prefixing with semantic payoff/cap prefixing.

The existing `not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt` in `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean` and `exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff` in `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean` concern minima in a semantic carrier. They do not supply actual realization, minimization of this observer objective J_r, or eventual full support. None of those is inferred here. The theorem's conditional force is exactly the exclusion in Section 1, within an actual branch once those hypotheses hold.

## 10. Lean handoff

A direct theorem shape quantifies over the exact reward table above, r>=0, and an actual stopping-law or behavioral profile with positive marginal Never masses, ALL-END, zero observer debts, observer-carrier minimality of J_r, and eventual full support. Its conclusion is eventual equality e_2,k=Q_2(q_k), followed by eventual zero debt for all players. An improving profile, a finite regular anchor, or eventual contact must not be assumed as a certificate field.

The mathematical components can be formalized separately: the rational energy and spectral calculations; exact root/debt/storage recursions; five-date rank and curvature; geometric decay from recurrent full contacts; the uniform tangent and weighted-Hessian estimates; analytic backward coordinates; the asymptotic matrix conjugacy and sign theorem; finite-dimensional Farkas/MFCQ and directional second-order necessity; and nested compact multiplier limits. The final adapter uses the stopping-law/behavior and literal-prefix declarations named in Section 9. The fixed control direction must be selected before the multiplier subsequence, and its derivatives must be proved truncation-independent.

The scope remains the exact specified table. No claim is made for arbitrary higher-coalition rewards, an open raw neighborhood, all four-player games, or the original shifted game's UE. The result supplies ordinary mathematical evidence for formalization; the new theorem and analytic components are not claimed as existing checked Lean declarations.
