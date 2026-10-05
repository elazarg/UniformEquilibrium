# A cyclic child with two joint phases: a raw all-parameter theorem

## 1. Raw class and strategic conclusion

Let I={0,1,2,3}. At each live date of a quitting game, the players
independently choose Continue or Quit. The first nonempty coalition S
of quitters absorbs with reward r(S), received thereafter. Never
absorbing has terminal reward zero. Strategies and unilateral deviations
may be arbitrary behavioral strategies; there is no public correlation
or extra information.

Take real parameters

    a,b,c,h_1,h_2,H>0,   D=abc−1>0,
    U,V≥1,   xi,eta>0,   p_1≤a−h_1,   p_2≤0.

For ANY R∈ℝ prescribe the five rows

    r(0)=(1,−h_1,−h_2,−H),
    r(1)=(U,0,b,−1),
    r(2)=(V,−1,0,c),
    r(3)=(R,a,−1,0),
    r(03)=(1+xi,p_1,p_2,eta).                         (1)

The only additional restrictions are six participant collision caps:

    r_1(01),r_1(13),r_1(013) ≤ min(−h_1,p_1),
    r_2(02),r_2(23),r_2(023) ≤ 0.                     (2)

Every remaining reward coordinate is arbitrary. In particular, there
is no restriction on the positive participant premiums at pair12, no
upper bound on eta, and no requirement that the greatest premium core
be proper. The own-singleton vector is s=(1,0,0,0).

**Theorem.** Every table satisfying (1)–(2), for every real R, has a
uniform-equilibrium payoff against unrestricted behavioral deviations.
One payoff vector is fixed before accuracy: for every epsilon>0 there
are one profile and one horizon threshold which deliver that vector
within epsilon and have regret at most epsilon at every larger horizon.

The inputs are finite raw reward inequalities. No hazards, continuation
values, equilibrium selector, or root certificate are supplied. The
proof produces two joint phases and two refinable solo phases on the
remaining interval between exact original-table source exits. It does
not assert completeness of that strategy architecture for arbitrary games.

The specialization p_1=−h_1,p_2=−h_2 is included directly, including
all cap equalities. The two independent halfspaces above do not rely
on reward closure or on an openness assertion for UE existence.

## 2. The remaining interval

Define

    A=[[0,−1,a],[b,0,−1],[−1,c,0]],
    A⁻¹=[[c,ac,1],[1,a,ab],[bc,1,b]]/D,
    nu=A⁻¹(h_1,h_2,H),
    R_low=1−[(U−1)nu_1+(V−1)nu_2]/nu_3,
    T=1−[c(U−1)+(V−1)]/(bc).                         (3)

All three coordinates of nu are positive. Section 7 proves UE for
R≤R_low and R≥T directly from the same original table, including
both equalities. If U=V=1, these thresholds coincide at one and those
exits cover the axis. Otherwise

    nu_3(T−R_low)
      =[c(U−1)h_2+(V−1)h_2+b(V−1)H]/(bc)>0.         (4)

It remains to construct the actual table on R_low<R<T≤1. Fix such
an R and put

    kappa=eta/(H+eta)∈(0,1),
    t=xi/(xi+1−R)∈(0,1),
    Y=D/[abc+a(c+1)(1+t)+t]∈(0,1).                   (5)

## 3. A global scalar selector

The four aggregate phases, repeated after each nonabsorbing date, are

    A: joint players 0,3 with hazards x,y;
    B: solo player 1 with hazard z;
    C: solo player 2 with hazard w;
    D: joint players 0,3 with hazards e,f.

For y∈(0,Y], and x in the admissible interval constructed below, set

    e=kappa*x/(1+kappa*x),   f=t*y/(1+t*y),
    C_A=(1−x)(1−y),        C_D=(1−e)(1−f),
    a_1=−h_1*x(1−y)+a(1−x)y+p_1*x*y,
    d_1=−h_1*e(1−f)+a(1−e)f+p_1*e*f+C_D*a_1,
    a_2=[h_2*e(1−f)+(1−e)f−p_2*e*f]/C_D,
    w=d_1/(1+d_1),
    z=[a_2+h_2*x(1−y)+(1−x)y−p_2*x*y]/[b*C_A].       (6)

Useful exact expansions are

    a_2=h_2*kappa*x+t*y−p_2*kappa*t*x*y,

    d_1={a(1+t)y−h_1(1+kappa)x
                 +[h_1−a+(1+kappa*t)p_1]xy}
                 /[(1+kappa*x)(1+t*y)],

    z={h_2(1+kappa)x+(1+t)y
                 −[1+h_2+(1+kappa*t)p_2]xy}
                 /[b(1−x)(1−y)].                    (7)

### Admissible rates, including a missing d_1 zero

For fixed y, d_1 strictly decreases in x. Apart from a positive
denominator, the negative of its derivative is

    h_1(1+kappa)
      +[a−h_1−(1+kappa*t)p_1+kappa*a(1+t)]y
       ≥h_1(1+kappa)+kappa(a+t*h_1)y>0.              (8)

Likewise z strictly increases, since the numerator controlling z_x is

    E_y=h_2(1+kappa−y)+t*y−(1+kappa*t)p_2*y>0.       (9)

At x=0, d_1=a(1+t)y/(1+t*y)>0 and
z=(1+t)y/[b(1−y)]<1. Indeed Y<b/(b+1+t); after cross
multiplication, the positive difference is (1+t)(ab+b+1).
As x→1, the numerator of z tends to E_y>0. Hence z=1 has a
unique root Z(y)∈(0,1), continuously depending on y.

Put

    A_y=a(1+t)y,
    B_y=h_1(1+kappa)−[h_1−a+(1+kappa*t)p_1]y.

When B_y≤0 set X(y)=Z(y); when B_y>0 set

    X(y)=min(Z(y),A_y/B_y).                           (10)

This does not presume a positive d_1 zero. In all cases 0<X(y)<1,
and throughout 0≤x≤X(y) we have 0≤w<1 and 0<z≤1. Before
the cap, w>0 and z<1; at the cap, w=0 or z=1. The cap is
continuous also at B_y=0, because A_y>0 and A_y/B_y tends to
+infinity from the positive side. Near y=0, B_y tends to the
positive h_1(1+kappa), so X(y)=O(y). All denominators are safe
on the admissible interval, including a collision of the two caps.

### Unique nonpivot root for arbitrary eta>0

Define

    Phi(x,y)=−z+(1−z)[c*w+(1−w)eta*e]
                            −x(H+eta)/(1−x).         (11)

At x=0 its sign for 0<y≤Y is the sign of
D−[abc+a(c+1)(1+t)+t]y. Thus Phi(0,y)>0 for 0<y<Y
and Phi(0,Y)=0. At x=X(y) its sign is negative: if z=1 this
is immediate, while at w=0 it follows from

    Phi≤eta*e−x(H+eta)/(1−x)<0.                     (12)

Global decrease of Phi need not hold for unrestricted eta. Instead,
localize every possible zero. Write g(x)=eta*e(x). If g≥c, then
c*w+(1−w)g≤g, and consequently

    Phi≤g−x(H+eta)/(1−x)<0,
    g=(H+eta)kappa²*x/(1+kappa*x).                  (13)

The strict inequality uses 0<kappa<1 and x>0. All zeros therefore
lie in the initial interval g<c. On that interval

    Phi_x=−z_x[1+c*w+(1−w)eta*e]
           +(1−z)w_x(c−eta*e)
           +(1−z)(1−w)eta*e_x−(H+eta)/(1−x)²<0.     (14)

The first term is negative, the second nonpositive, and the last two
together are negative because

    eta*e_x=(H+eta)kappa²/(1+kappa*x)²
                              <(H+eta)/(1−x)².

The initial positive sign and negative cap sign now produce a UNIQUE
root x(y)∈(0,X(y)) for every y∈(0,Y). If g reaches c before the
cap, (13) gives the negative sign already there; later roots are
excluded. At the root Phi_x<0, so its dependence on y is continuous.
The bounds (10) give x(y)→0 as y→0. At y→Y, any positive
accumulation point is excluded by (13) or by strict decrease from
Phi(0,Y)=0 in the initial g<c interval. Hence x(y)→0 there too.
Near Y, X(Y)<1 keeps all denominators uniformly nonzero.

At the zero endpoint, direct differentiation gives

    Phi_x(0,0)=−(1+kappa)(H+c*h_1+h_2/b)<0,
    Phi_y(0,0)=(1+t)(ac−1/b)>0.

The first-order expansion, using x=O(y), yields

    x/y → (1+t)/[(1+kappa)nu_3],
    z/y → (1+t)nu_1/nu_3,
    w/y → (1+t)nu_2/nu_3.                            (15)

The terms involving p_1,p_2 in (7) change only coefficients of xy,
so they do not alter these derivatives. No global continuation theorem
is being assumed: existence and uniqueness were proved separately on
every admissible interval.

### The pivot equation crosses on that branch

Along x(y), put

    c_0star=w(V−1)+(1−w)xi*f,
    b_0=z(U−1)+(1−z)c_0star,
    F(y)=(R−1)y+(1−y)b_0−xi*y.                     (16)

Since xi(t−1)=t(R−1), (15) gives

    lim_(y→0) F(y)/y=(1+t)(R−R_low)>0.              (17)

At y=Y the limiting x=e=0 gives

    z=D/[b(ac+a+1)],    w=D/[c(ab+b+1)],
    F(Y)/Y=(1+t)(R−T)−t*xi*D/(abc)<0.              (18)

These identities follow by substituting (5)–(7), first at x=0 and
then in (16). Continuity and the intermediate value theorem produce
an interior y with F(y)=0. Fix one such y and its uniquely selected
x. All six hazards x,y,z,w,e,f are now strictly between zero and
one, produced solely from the given reward table.

## 4. All actual phase identities and joint deviations

Define the actual payoff vectors

    V_A=(1+xi*y,a_1,a_2,eta*x),
    V_B=(1+b_0,0,b*z,x(H+eta)/(1−x)),
    V_C=(1+c_0star,0,0,c*w+(1−w)eta*e),
    V_D=(1+xi*f,d_1,0,eta*e).                        (19)

We check every policy and Continue identity, retaining all simultaneous
coalitions. The scalar subtraction of one in player 0's equations is
only algebra; Never still pays zero in the original game.

At joint row D, player 0's Continue equation is

    (R−1)f+(1−f)xi*y=xi*f,

which is exactly the definition of f. Its Quit value is 1+xi*f.
Player 3's Continue equation is −H*e+(1−e)eta*x=eta*e, exactly
the definition of e, and its Quit value is eta*e. At A, their Quit
values are 1+xi*y and eta*x. Their Continue equations are respectively
F=0 and

    −H*x+(1−x)[x(H+eta)/(1−x)]=eta*x.

Thus both joint players are indifferent at both occurrences.

For player 1, the next B value is zero, so its A Continue value is
the three-term absorbing contribution a_1 in (6). At D, the same
contribution with e,f plus C_D*a_1 gives d_1. The identity

    −w+(1−w)d_1=0

enforces its C equation and hence its B owner Continue value zero.
Its forced-Quit value at its B solo occurrence is its singleton zero.

For player 2, its D Continue value vanishes by the definition of a_2.
The definition of z is precisely its A identity with next B value
b*z. The B equation gives b*z since its next C value is zero. Its
C owner Continue and Quit values are both zero because its next D
value is zero. The remaining player-0 and player-3 equations at B,C
are the definitions of b_0,c_0star and Phi=0. These checks establish
all sixteen Continue identities; combining them with supported Quit
indifference establishes all sixteen policy identities.

Every coordinate of V_B,V_C,V_D is at least its own singleton. This
uses U,V≥1, a_2>0, d_1>0 and the positive rates. A's player-1
coordinate a_1 may be negative; no floor is imposed there.

At A, player 1's forced-Quit endpoint is

    x(1−y)r_1(01)+(1−x)y*r_1(13)+xy*r_1(013).

The three caps in (2) bound its terms by the corresponding actual
passive rewards −h_1,a,p_1. It is therefore at most a_1. At D,
the same capped entries are all nonpositive, so its Quit endpoint
is at most zero, less than d_1. Player 2's two joint Quit endpoints
are nonpositive by the other three caps, while its displayed values
are a_2>0 and zero. Thus both joint rows have exact Quit caps for
every player, including the simultaneous-opponent coalition {0,3}.

## 5. Refinement and unrestricted terminal deviations

For each integer n≥1 replace B and C by n solo dates with respective
hazards

    beta_n=1−(1−z)^(1/n),
    gamma_n=1−(1−w)^(1/n).                           (20)

Retain A,D without modification. Each period has m_n=2+2n dates.
The aggregate survival of each solo block is unchanged, and absorption
within it always uses the same singleton coalition. Hence the macro
terminal law, phase values, and target V_A are independent of n.

Inside a block with owner j, microhazard b and k remaining microdates,
the actual value is

    [1−(1−b)^k]r({j})+(1−b)^k V_next.

For 0≤k≤n, these values lie on the segment between the two MACRO
endpoint values. Both endpoints have singleton floors on B→C and
C→D. Those floors therefore hold throughout these arcs, even though
the singleton reward vector r({j}) itself need not have all floors.
The owner's coordinate equals its singleton throughout. Every Continue
equation remains exact, and the owner is exactly indifferent.

Let

    C_join=max(0,r_i(ij)−s_i : j∈{1,2}, i≠j),
    delta_n=C_join*max(beta_n,gamma_n)→0.             (21)

At a solo microdate, an outsider's Quit value is
(1−b)s_i+b*r_i(ij)≤s_i+b*C_join≤V_i+delta_n.
The owner's Quit value equals its value. At retained joint rows the
exact bounds of Section 4 apply without error. This proves one common
Quit error at every date, not a bound accumulating with the period.

Indeed, add delta_n to every coordinate of the bounded value path.
Quit is bounded by this augmented value. Continue transports only the
opponents' nonabsorption probability times the added constant, which
is at most that constant. Thus the augmented path is a Bellman
supersolution at every history for every mixed action of a deviator.
This argument remains valid at a negative coordinate of V_A.

The four opponent survival probabilities per complete period are

    rho_0=(1−y)(1−f)(1−z)(1−w),
    rho_1=(1−x)(1−y)(1−e)(1−f)(1−w),
    rho_2=(1−x)(1−y)(1−e)(1−f)(1−z),
    rho_3=(1−x)(1−e)(1−z)(1−w).                     (22)

They are strictly below one and independent of n. Opponents' fixed
date-dependent independent coins can be presampled for the proof; no
deviator observes future coins. Their first scheduled Quit bounds the
actual absorption date from above under ANY behavioral replacement.
Survival after k periods is therefore at most rho_i^k, uniformly over
the deviator. Finite Bellman comparison followed by this geometric
tail makes its bounded remainder vanish. Every complete unilateral
terminal payoff is at most V_A,i+delta_n. Policy equality and the
same vanishing tail give prescribed terminal payoff exactly V_A.

If C_join=0, the unrefined cycle itself is exact terminal Nash. In
general the refined profiles are approximate, with one fixed target.

## 6. Uniform horizons and finite stopping laws

Let M≥0 bound every absolute reward coordinate of the fixed table.
By (22), the prescribed profile and every unilateral replacement have
expected absorption date bounded by

    K_n=m_n*max_i 1/(1−rho_i).

The difference between expected N-date average payoff and expected
terminal payoff is at most 2M*K_n/N, uniformly over all replacements:
pathwise the discrepancy is bounded by 2M times the number of dates
before absorption divided by N. Thus the prescribed delivery error
is at most 2M*K_n/N and full N-horizon regret is at most

    delta_n+4M*K_n/N.

Choose n for accuracy, then one N threshold. The same profile works
for every larger horizon, and the target remains V_A. This proves the
uniform claim on the constructed interval with the required quantifiers.

There is also a finite independent-stopping-law version. Each player's
aggregate period survival is respectively

    lambda_0=(1−x)(1−e), lambda_1=1−z,
    lambda_2=1−w,       lambda_3=(1−y)(1−f).

Censor its stopping law after K periods by transferring its remaining
mass to Never. The sum of transferred marginal masses is
tau_K=sum_i lambda_i^K→0. Product coupling bounds target error by
2M*tau_K and full terminal regret by delta_n+4M*tau_K. For a
fixed complete deviation, compare only the opponents' changed laws;
then compare prescribed payoffs. Both bounds are uniform over the
deviator. Choosing n and then K gives finite independent laws with
vanishing full regret and delivery error around the same target.

## 7. Exact original-table exits and equality boundaries

For a real matrix Gamma, an LCP root at offset q is u≥0 with
q+Gamma*u≥0 and u_i(q+Gamma*u)_i=0 for every i. Gamma is R₀ if
the zero-offset problem has only the zero root. We use four tracked
facts, whose declarations are named in Section 9:

- At a regular finite-root offset, an R₀ matrix's degree is the sum
  of the signs of its active principal determinants. Inactive residuals
  must be strictly positive and those determinants nonzero.
- An original quitting game's R₀ singleton matrix with degree different
  from one supplies an original-game uniform-equilibrium payoff.
- In Fin4, absence of such a payoff forces the singleton matrix to be
  R₀, of degree one.
- A three-player child's nonnegative inverse and nonnegative actual
  outside singleton-row inverse weights supply a parent-game UE.

The singleton-difference matrix for (1) is

    Gamma=[[0,U−1,V−1,R−1],
           [−h_1,0,−1,a],
           [−h_2,b,0,−1],
           [−H,−1,c,0]].                            (23)

For R≠R_low it is R₀. If a homogeneous root has positive pivot p,
the child inequalities force all three child coordinates positive.
Their equations give child vector p*nu. The pivot residual is then
p*nu_3(R−R_low), which complementarity forces to vanish, impossible.
If the pivot is zero, the cyclic negative child edges propagate any
positive child coordinate to all three, where invertibility of A
would force the zero vector. Thus no nonzero homogeneous root exists.

For R<R_low put d=nu_3(R_low−R)>0 and choose q_0>d. At offset
(q_0,−h_1,−h_2,−H), all child coordinates are strictly positive by
their three inequalities, and equal (1+p)nu. The pivot residual is
q_0−d(1+p). There are exactly two roots:

    p=0,          child=nu;
    p=q_0/d−1>0,  child=(q_0/d)nu.

The first inactive pivot residual is q_0−d>0 and its active determinant
is D>0. The second has every coordinate active and determinant

    det Gamma=D*nu_3(R−R_low)=−Dd<0.

The regular root-sum degree is therefore zero, giving UE directly.
At R=R_low, the positive vector (1,nu) is a nonzero homogeneous LCP
root. The Fin4 no-UE implication to R₀ gives UE by contraposition.
No limiting profile is needed on this equality boundary.

For R≥T, the actual passive inverse weights of child123 are

    [c(U−1)+(V−1)+bc(R−1),
     ac(U−1)+a(V−1)+(R−1),
     (U−1)+ab(V−1)+b(R−1)]/D.                       (24)

At R=T they are 0, [c(U−1)+(V−1)]/(bc), and (V−1)/c. All
are nonnegative and increase with R. The inverse A⁻¹ in (3) is
strictly positive. The raw passive-inverse theorem consequently gives
UE, including R=T. This uses the original table, not a supplied child
equilibrium, and imposes no extra condition on simultaneous rewards.
Together with Sections 3–6, all real R are covered.

## 8. Exact tests and scope boundaries

### Two disjoint premium traps and no pure exit

Take a=b=c=2, h_1=h_2=1, U=V=2, p_1=1, p_2=−1/2, and

    H=188295644/24220715,
    eta=564886932/24220715=3H>c,
    xi=176348713/95068097,
    R=−81280616/95068097.

This is on the p_1=a−h_1 boundary and has a positive joint outsider
reward. Proper exact rates are

    x=1/100, y=1/20, e=3/403, f=1/41,
    z=2939/60192, w=2123/18646.

They give a_1=9/100, a_2=1043/32000, d_1=2123/16523 and

    R_low=−661769792/497694863 < R < 1/4=T.

Use the five rows (1), and complete the other ten rows by

| S | r(S) |
|---|---|
| 01 | (0,−1,100,100) |
| 02 | (0,100,0,100) |
| 12 | (100,1/2,1/2,100) |
| 13 | (100,−1,100,0) |
| 23 | (100,100,0,0) |
| 012 | (−100,−100,−100,100) |
| 013 | (−100,−100,100,−100) |
| 023 | (−100,100,0,−100) |
| 123 | (100,−100,−100,−100) |
| 0123 | (−100,−100,−100,−100) |

Exact rational substitution gives all sixteen policy and all sixteen
Continue identities and all eight retained-joint Quit caps.

A premium trap is a nonempty A for which each i∈A has some coalition
S⊆A containing i with r_i(S)>s_i. In this table the only traps are
03,12,0123, so there are two disjoint traps and the greatest premium
core is full. Every player has a negative premium at the grand coalition.

No pure absorbing coalition is an equilibrium. At singletons 0,1,2,3,
players 3,3,1,0 respectively profit by joining. At pairs 01,02,12,13,23,
players 0,0,2,1,3 respectively profit by withdrawing. At 03, player 2
profits by joining, from −1/2 to zero. At triples 012,013,023,123,
players 0,0,0,1 respectively profit by withdrawing to passive reward
100. At the grand coalition player 0 does so. All Never is defeated
by the positive singleton of player 0.

Trap03 has two strictly positive join gaps: 1+xi−R and eta+H.
Neither member weakly leaves that trap. Hence a protected support-
specific-leave test or a positive-weight aggregate-leave test cannot
certify it. A pair-core test cannot apply since the greatest core is
full. Product-low fails at the sure law on03, with both active Quit
payoffs above their own singleton. These are precise bounded comparisons,
not an exhaustive exclusion of every stationary or chronological producer.

### A genuinely negative retained-joint value

Take a=b=c=2, h_1=10, h_2=1, U=V=2, p_1=−10,p_2=−1, and

    H=12507608845790/1340190709031,
    eta=1250760884579/1340190709031,
    xi=4829928386673/466635169733,
    R=−210070619692/1399905509199.

Exact rates and scalar values are

    x=1/500, y=1/100, e=1/5501, f=9/1009,
    z=116399/10868220, w=88690/5639199,
    a_1=−1/25000, a_2=50509/5500000,
    d_1=88690/5550509,
    R_low=−30821872992215/79963036761851 < R < 1/4.

Both residuals vanish exactly. Set the first three caps to −10, the
last three to zero, and every other unused coordinate to 37. The full
policy/Continue identities and joint Quit caps still hold, despite
V_A,1<0. The refined solo arcs have all required floors. This is an
algebra and regret-regression, not a broad noncoverage witness: the
grand coalition of this completion is a pure equilibrium. Requiring
singleton floors at EVERY phase would nonetheless reject this valid
constructed profile and its literal complete-deviation proof.

### A cap without any positive d_1 zero

Take a=b=c=2, h_1=1/100, h_2=H=eta=xi=1, U=V=2,
R=0, p_1=199/100, p_2=−1/2. Then kappa=t=1/2,
R_low=−799/304<R<T=1/4 and Y=2/5. At y=1/5,

    B_y=−169/2000<0,   X(y)=Z(y)=52/113.

The d_1 numerator is positive for every x≥0, while z reaches one
at the stated cap. This tests the otherwise missing branch in (10);
the theorem must not assume that both hazard caps have finite roots.

At the other raw boundary p_2=0, the constructive interval itself has
a pure-pair exit: both members strictly prefer joining 03, while (2)
prevents either outsider from joining profitably. The analytic selector
still works there. That boundary is included, not asserted to provide
nontrivial separation from pure-equilibrium criteria.

## 9. Tracked source dependencies and implementation shape

The original-table exits use these exact declarations:

- `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`.
- `exists_finset_r0Degree_eq_sum_sign_det` in
  `MathUE/LinearProgramming/R0DegreeSum.lean`.
- `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
  `UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`.
- `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
  in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

The constructive consumer has the literal shape of
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`,
`QuittingInfinitePathQuitErrorCertificate.isεAsymptoticNash_and_delivers`,
and `isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
Their bounded-value, exact-Continue and common Quit-error obligations
are verified in Sections 4–6; they do not require an all-phase singleton
floor. The direct horizon proof above independently identifies the
complete behavioral and fixed-target quantifiers.

The implementation shape is a finite raw predicate (1)–(2), followed
by a helper producing the unique admissible root of (11) with its two
endpoint limits, the pivot crossing (17)–(18), rates and phase vectors,
and arbitrarily accurate profiles around (19). The two exact singleton
source exits then supply the all-R theorem. The new obligation is this
raw selector and its revised cap, not a new refinement or UE compiler.
Singleton floors belong only to the two refined solo arcs; the retained
joint rows are discharged by their actual Quit comparisons.
