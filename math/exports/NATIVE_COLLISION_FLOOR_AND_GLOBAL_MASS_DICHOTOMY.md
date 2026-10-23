# Collision-sparse native tails force absorbing approximate Nash play

Complete ordinary mathematics. No new Lean declaration, implementation or
build is claimed. The arbitrary signed four-player quitting-game
uniform-equilibrium payoff conjecture remains OPEN.

This packet proves a quantitative ACTUAL-law bound from ORIGINAL complete
debt and cross-owner finite pair-collision mass, then proves its transport
to the ORIGINAL retained source and every old conditional suffix. No actual
exact-Nash realizer, geometric tail, minimizing suffix, bounded calendar or
deleted-clock divergence is assumed. It consumes tails whose relative
shared collision tends to zero, while retaining dense shared bursts as a
precise remaining geometry.

## 1. The quantitative statement

Fix four owners and a bounded real first-quitting reward table Z with
Z_i({i})=0. Literal AllNever and live play pay zero. Let M>=1 bound every
absolute reward. An actual profile consists of four independent complete
laws on Nat and a separate Never point. Every unilateral replacement is
an arbitrary complete independent law. Define

    U_i = prescribed payoff,
    F_i(t) = payoff from pure deadline t, or literal Never,
    B_i = sup_t F_i(t), d_i=B_i-U_i, D=SUM_i d_i,
    A = inf{D(P): P ACTUAL and absorbing almost surely}.

Every mixed complete response averages the pure values. These are therefore
the unrestricted complete behavioral caps, including every finite date and
Never. All debts are nonnegative.

For ANY supplied actual profile Q, not assumed Nash, write

    p_i(n)=Q_i({n}), f_i=SUM_n p_i(n), beta=SUM_i f_i,
    C=SUM_n SUM_(i<j) p_i(n)p_j(n).

Assume 0<beta<=1/2. Its original Never masses are at least 1-beta.

**Theorem.** At the SAME fixed table,

    A <=400M [D(Q)/(M beta^2)+4sqrt(C)/beta]^(1/9).    (1)

The right side is interpreted as zero when both terms vanish. All
constructed profiles are actual private independent stopping laws on Nat.
No sign, genericity, matrix rank, tail rate, local minimality, common
cohort, or exact-contact selection hypothesis is used.

In particular D=o(beta^2) and C=o(beta^2) along any actual sequence at
the SAME table imply A=0. For exact full Nash this asymptotic implication requires only
C=o(beta^2), and allows large almost-solo atoms as well as many small
shared atoms. The proof does NOT bound all born-query error by O(C).

## 2. One supported-atom inequality with OLD complete debt

Delete dates with no atoms and retain the order of all occupied dates.
This changes no prescribed payoff, finite mass, Never mass or C, and
loses only old offered responses. If support is finite, every later
finite query equals Never because own singleton is zero. We may work
on this compressed clock. In all upper bounds retain the ORIGINAL
caps B_i, so dropping old responses cannot invalidate a bound. The
original identity

    d_i=SUM_n p_i(n)[B_i-F_i(n)]
                  +(1-f_i)[B_i-F_i(Never)]             (2)

still holds with these caps. It follows by complete-law Fubini and every
summand is nonnegative. Empty deleted dates had zero own mass.

Fix an old occupied date n, and let v_i(n+1) be the old prescribed
conditional payoff after the WHOLE date. Write P_i(n)=SUM_(j!=i)p_j(n).
Let H_-i(n) be old opponent survival before n and c_-i(n) their
conditional joint Continue at n. Conditional opponent hazards are at
most 2p_j(n), and

    H_-i(n)c_-i(n)>=PRODUCT_(j!=i)(1-f_j)>=1-beta>=1/2.

Compare pure deadline n with the legal complete response that waits
through n and then uses i's ORIGINAL conditional law after n. Both have
the same passive prefix against opponents. If Q_i(n) is immediate Quit
and A_i(n) the passive current-coalition numerator, the second response
has value

    F_i(n)+H_-i(n)[A_i(n)+c_-i(n)v_i(n+1)-Q_i(n)].

It is at most B_i. Put g_i(n)=B_i-F_i(n)>=0. Own solo zero gives
|Q_i(n)-A_i(n)|<=2M times the conditional probability of some current
opponent atom, at most 4MP_i(n). Therefore

    (v_i(n+1))_+ <=2g_i(n)+8MP_i(n).                (3)

No Nash premise or nonnegative-rent premise was used. Multiplying by
old own atoms and using (2) controls the g terms by OLD debt; debt after
editing laws is not substituted into this charge.

## 3. Hybrid clock: delete minorities at big shared dates

Fix epsilon>0. At every old shared date whose mixture mass
a_n=SUM_i p_i(n) exceeds epsilon, choose one dominant owner, keep its
atom whole, and move every other owner's atom at that date to its OWN
literal Never. Let E be the total mass removed. At small shared dates
keep all atoms. Let

    C_s=SUM_(n:a_n<=epsilon) SUM_(i<j)p_i(n)p_j(n).

Thus

    C_s<=epsilon beta/2.                              (4)

At a big shared date let b_n be its largest atom and l_n=a_n-b_n.
Since b_n>=a_n/4>epsilon/4, the pair sum at that date is at least
b_n l_n>epsilon l_n/4. Consequently

    E<=4C/epsilon.                                    (5)

No occupied old date disappears: its dominant atom stays. Serialize
the remaining SMALL shared dates into consecutive singleton subdates,
in any fixed owner order. Keep all solo and all dominant large atoms
whole. There are no extra empty slots within blocks. The output R is
an actual singleton calendar, with total finite mass beta_R=beta-E.

Deleting total mass E changes any prescribed payoff and any fixed pure
response by at most 2ME under independent coupling. The same uniform
bound passes to each full cap, so total debt increases by at most16ME.
For serialization, prescribed payoff errors are at most 2MC_s. A new
query within a small block is compared with the old query AT that
block. Outside the event of an opponent in the block, of probability
at most epsilon, and an opponent pair collision, of probability at
most C_s, outcomes agree. Whole solo blocks have no within-block error.
Never has only collision error. Every finite post-LAST response equals
Never. These price the ENTIRE new menu and imply

    D(R)<=D(Q)+16ME+8M epsilon+16MC_s
         <=D(Q)+16M(E+epsilon).                       (6)

The last inequality uses beta<=1/2 and (4). No selected-query family
or interchange of a supremum and a limit is used.

## 4. The positive-own-continuation charge of the hybrid clock

Consider a kept old atom p_i(n), now a singleton subdate. Compare its
new prescribed conditional continuation AFTER that subdate with the
old prescribed conditional continuation after the WHOLE old date n.

Use intermediate profiles after the WHOLE current block, before and after
censoring and future serialization; compare the final R after its own
subdate with that final whole-block continuation separately.

First, censoring total mass E changes the whole-block conditional laws
by total variation at most 4E across owners. This includes removed atoms BEFORE
the cut: moving them to Never changes the denominator. One direct bound
for each owner is twice its unconditional total variation divided by
the smaller remaining survival, which is at least1-beta>=1/2. The
prescribed-payoff error is therefore at most8ME.

Second, IN THE FINAL SERIALIZED R, if the current block was small and
shared, some other subdates may still lie ahead. Comparing its continuation
after the own subdate with its continuation after the WHOLE block changes
the product law by at most2P_i(n), hence payoff by at most4MP_i(n).
There are no such remaining current atoms at a retained big dominant
date, but the same upper bound is harmless.

Third, serializing FUTURE small shared blocks costs at most8MC_s:
each post-cut marginal survival is at least1-beta>=1/2, so the future
conditional pair-collision union bound is at most4C_s.

Combining with (3), every new own continuation satisfies

    (v_i^R(after own subdate))_+
       <=2g_i(n)+12MP_i(n)+8ME+8MC_s.               (7)

The first-exit mass at that new own subdate is at most its kept old
unconditional atom p_i(n). In the singleton calendar write H_l for
joint survival before subdate l, q_l for its sole hazard, and h_l for
its owner. Define the NONNEGATIVE charge

    T_R=SUM_l H_l q_l (v_(h_l)^R(l+1))_+.

Equation (2) bounds the sum of kept p_i(n)g_i(n) by D(Q). At small
shared dates, SUM_i p_i(n)P_i(n) is twice their pair sum. At big dates
only the dominant atom survives, and its p_i(n)P_i(n)=b_n l_n<=beta l_n.
Thus

    SUM_(kept atoms) p_i(n)P_i(n)<=2C_s+beta E.

Weight (7) by kept atoms, sum, and use beta<=1/2:

    T_R<=2D(Q)+28MC_s+20M beta E
       <=2D(Q)+20M beta(E+epsilon).                 (8)

All series in this charge are nonnegative monotone sums. The proof
does not control an unweighted sum of absolute rents or silently drop
negative continuation values.

## 5. Dilate first-exit masses and price every complete response

Suppose E<=beta/2, so beta_R>=beta/2. The joint Never mass nu_R of R
satisfies beta_R/2<=a_R=1-nu_R<=beta_R. Indeed the union lower bound
is at least beta_R-SUM_(i<j) f_i^R f_j^R>=beta_R-beta_R^2/2.
If R has a finite LAST, extend its stages by q_l=0, arbitrary owner
labels and zero conditional values afterward; this includes every
post-LAST natural deadline. For delta in(0,1), put
lambda=(1-delta)/a_R<=4/beta and define the actual singleton dilation

    H'_l=1-lambda+lambda H_l,
    q'_l=lambda H_lq_l/H'_l,
    c_l=lambda H_l/H'_l.

All H'_l>=delta. The new independent laws have joint Never delta,
each individual Never at least delta, and conditional prescribed and
immediate-Quit values v'_i(l)=c_l v_i^R(l), Q'_i(l)=c_l Q_i^R(l).

The exact deleted-own-law recursion, for EVERY finite deadline b, is

    F'_i(b)-U'_i
      =SUM_(l<b:h_l=i) S'_-i(l)q'_l v'_i(l+1)
               +S'_-i(b)[Q'_i(b)-v'_i(b)].           (9)

Here S'_-i is new opponent survival. To derive(9), track
P'_i(l)+S'_-i(l)v'_i(l), where P'_i is passive opponent absorption
before l. At another owner's stage its change is zero by the actual
Bellman equation. At an own stage its increase is exactly
S'_-i(l)q'_l v'_i(l+1), because the DELETED own law no longer supplies
the prescribed stopping hazard. Summing these identities and replacing
the terminal continuation by the forced-current payoff gives(9).
No Nash or transversality assumption is used. Its coefficient bounds are

    S'_-i(l)q'_l c_(l+1)<=(lambda/delta)^2 H_lq_l,
    S'_-i(b)c_b<=(lambda/delta)H_b.

Copying R's own law before b and forcing Quit at b is a legal complete
replacement, so

    H_b[Q_i^R(b)-v_i^R(b)]_+<=d_i(R).

Use positive parts in (9), (6), (8), and lambda<=4/beta. This gives

    D(R')<=(lambda/delta)^2 T_R+(lambda/delta)D(R)
      <=34D(Q)/(beta^2 delta^2)
                 +384M(E+epsilon)/(beta delta^2).   (10)

This prices every finite response uniformly. Native own singleton zero
implies F'_i(b)->F'_i(Never): any finite opponent first exit eventually
precedes b, while late own solo and AllNever both pay zero on the
all-opponent-Never branch. Bounded convergence applies. Thus (10)
prices literal Never and every complete mixed replacement too.

Move the smallest new marginal Never mass, at most delta^(1/4), to
one finite date. That owner becomes finite almost surely, so the new
ACTUAL profile absorbs almost surely. Four prescribed values and the
three other caps change by at most2M delta^(1/4) each; its own cap is
unchanged. Consequently

    A<=34D(Q)/(beta^2 delta^2)
       +384M(E+epsilon)/(beta delta^2)+14M delta^(1/4). (11)

## 6. Optimize the cutoff and retain the original debt

If C>0, set epsilon=2sqrt(C). Then E<=2sqrt(C) and
E+epsilon<=4sqrt(C). Put

    r=D(Q)/(M beta^2)+4sqrt(C)/beta.

If r<1, then E<beta/2 and all preceding steps apply. Choose
delta=r^(4/9). To verify the constant, put u=D(Q)/(M beta^2)
and v=4sqrt(C)/beta, so u+v=r. In(11), the first two terms are
at most M*(34u+384v)/delta^2<=384M r^(1/9); the last is
14M r^(1/9). Hence A<=398M r^(1/9), proving(1).
If r>=1, any actual absorbing profile has D<=8M, which proves (1)
directly. If C=0, use the existing singleton clock with no deletion or
serialization and let epsilon tend to zero in the same estimates;
equivalently set E=epsilon=0. If also D=0, let delta tend to zero.
This covers r=0 and completes the proof.

Under A>0, every actual profile with0<beta<=1/2 must therefore satisfy

    D(Q)/(M beta^2)+4sqrt(C)/beta >=(A/(400M))^9.      (12)

For actual exact full Nash, this forces

    C/beta^2 >=(1/16)(A/(400M))^18.                 (13)


## 7. Cross-owner pair kernels and arbitrary retained debt

The compact original-N carrier, its actual realizing profiles and its
complete mean-law compiler are proved in Section10. Let q be ANY one
such retained representation at the fixed native table, with full debt
D_Z(q), total finite mass beta, and

    C(q)=SUM_(i<j) SUM_(finite retained atoms x)
                                      q_i({x})q_j({x}).

This is a CROSS-OWNER finite collision coordinate. It is neither a
same-owner square nor a collision-maximizing selector, and literal
Never pairs are excluded. All finite mass, including nonatomic mass,
is counted in beta. Assume0<beta<1/2.

Take the ACTUAL realizing sequence and the SAME raw charts used by its
compiler. For each pair i,j let K_m(x,y) indicate that both raw coordinates
are finite and belong to the SAME OLD atom interval. Exclude the
finite/Never boundary, the countably many endpoints of POSITIVE limiting
atom intervals and the raw diagonal. These are null. The WHOLE limiting
endpoint set E may have positive measure and is NOT discarded.

Off this null set, two finite raw coordinates are either inside the SAME
positive limiting interval, hence eventually the same old interval, or
have a limiting endpoint strictly between them, hence eventually distinct
old intervals. Thus K_m converges almost everywhere and in L1 to the
indicator K of a shared finite retained atom. The raw Never interval is
excluded throughout; no escaping finite mass is relabeled as a pair.

The independent owner densities are bounded by4. Their twofold products
converge against fixed L1 kernels: test rectangles, then finite rectangle
sums, then approximate arbitrary L1 functions using the uniform bound16.
Split the integral with K_m into the changing-kernel L1 error and the
fixed-K density test. This proves for EVERY pair

    SUM_n Q_i^m({n})Q_j^m({n})
                 ->SUM_x q_i({x})q_j({x}).             (P1)

Summing six pairs gives C(Q^m)->C(q). Exact ORIGINAL Never convergence
gives beta_m->beta. The compiler also gives U^m->U, B^m->B and hence
D_Z(Q^m)->D_Z(q), whether or not that debt is zero. This is a special
old-interval kernel convergence, not continuity of equality under arbitrary
weak convergence of probability measures.

For all large m,0<beta_m<=1/2. Apply(1) to these ACTUAL profiles and pass
to the limit using continuity. The result is the FULL retained version

    A<=400M[D_Z(q)/(M beta^2)+4sqrt(C(q))/beta]^(1/9). (P2)

No exact-Nash actual representative is required. The collision value may
depend on the chosen faithful retained representation; the same bound
holds for EVERY such compiled representation. No inheritance of a
collision selector or an optimizing suffix is asserted.

## 8. Conditional actual realizers at every old survival cut

Let the retained original-N representation now have native debt zero and
every original N_i>0. Fix ANY old survival cut, and let s_i be the total
mass surviving to that cut, including its Never atom and the WHOLE current
atom when the cut is a supported date. Thus s_i>=N_i>0. Conditional laws
remain independent; their original Never coordinates are N_i/s_i.
Past opponent absorption adds the same constant to every subsequent
pure query, and opponent survival multiplies each conditional value by
one positive scalar. Zero native debt and positive own Never therefore
make conditional Never a best reply, and every prescribed conditional
finite atom attains it by Fubini. The retained conditional profile is
FULL native Nash, not a separately minimizing suffix.

To justify its ACTUAL access, use the original actual realizing profiles
and choose MATCHING old offered cuts. At a positive retained atom, take
the corresponding WHOLE old atom: survival to its DATE starts at its
LEFT raw interval boundary, never halfway through the raw interval. The
offered query is its midpoint label, which represents the entire atom.
At a nonatomic cut choose approaching old offered queries; its equality
boundary has zero mixture mass. Cut-survival indicators and their products
converge almost everywhere by the same original raw argument. The cut's
survival masses s_i^m converge to s_i and stay uniformly positive.

Condition EACH ACTUAL marginal on survival to that whole old cut. These
are legal independent ACTUAL complete laws, with their original tail
calendar reindexed on Nat. There is no inserted prefirst response: the
old cut query is suffix date zero. At a positive atom it retains that
whole current atom. If a later cut is empty, it is still the original
offered empty query. The absolute calendar is otherwise only translated.

For any owner i copy its OLD own law before the cut, and on its old own
survival use an arbitrary conditional full deviation. The gain over its
old prescribed payoff is EXACTLY the original JOINT cut-survival H_m
multiplied by the conditional gain. The passive prefix cancels. Taking
suprema therefore proves, before ANY limit,

    d_i(Q^m_cond)<=d_i(Q^m)/H_m,
    D_Z(Q^m_cond)<=D_Z(Q^m)/H_m ->0,                 (P3)

since H_m=PRODUCT_i s_i^m stays bounded away from zero by the original
Never product. No unproved contact persistence, conditional optimizer or
actual exact-Nash realizer has been inserted.

The conditional pair-equality kernels are K_m restricted to both surviving
coordinates and divided by s_i^m s_j^m. Their limiting denominators are
positive, and the densities are uniformly bounded by4/min_i s_i^m.
The same L1 changing-kernel and independent-density argument proves their
collision convergence. Conditional finite masses and original Never
converge as well. Thus if the retained conditional total finite mass
satisfies0<beta_cut<1/2, apply(1) to these ACTUAL conditional realizers
and pass to the limit. Its conditional collision obeys

    C_cut/beta_cut^2 >= c_A,
    c_A=(1/16)[A/(400M)]^18 when A>0.                (P4)

This is an ACTUAL-source proof of the conditional statement, not an
assumption that every abstract compact-calendar Nash law is executable.
The actual-realizer argument is primary; the conditional Nash contacts
identify its limiting debt but do not replace it.

## 9. Produced bursts and a full-calendar raised-minimum mass bound

For any complete profile, retained or actual, let s be the supremum over finite
atoms of the SECOND-LARGEST owner atom mass at that date. For each pair
at an atom, its smaller factor is at most s. Assign the product to its
larger factor; each owner atom is charged at most three times. Hence

    C<=3s beta.                                      (P5)

If A>0 and the law is exact retained native Nash with0<beta<1/2,
equation(P4), or(P2) directly, gives s>=c_A beta/3. Positive s is attained:
only finitely many owner atoms can exceed any fixed positive threshold,
because their total finite mass is finite. Thus there is a finite date
with TWO DISTINCT owner atoms each at least c_A beta/3. The same statement
holds at EVERY old conditional cut with0<beta_cut<1/2. Its beta and atom
masses are those of the CONDITIONAL laws, explicitly defined in Section8.
If desired the original atoms at that cut are at least min_i N_i times
these lower bounds, since s_i>=N_i.

Consequently any sequence of nontrivial old conditional suffixes with
beta_cut->0 has C_cut not=o(beta_cut^2). In a positive-original-N source,
conditional finite mass tends to zero along genuinely terminal cuts whose
remaining finite mass tends to zero. Each such small tail must contain a
pair-macroscopic burst; singleton tails, purely nonatomic tails and tails
with vanishing relative cross-owner collisions are consumed. Dense bursts,
finite macroscopic LAST and nonvanishing terminal mass are not excluded.

There is also a useful ORIGINAL global-minimum consequence, without a
finite support bound. Put k=[A/(400M)]^9>0. Equations(1) and(P2) imply
for EVERY actual or retained profile with0<beta<1/2

    D_Z/(M beta^2)+4sqrt(C)/beta>=k.                  (P6)

At a raised original GLOBAL minimum for r_i=theta_i(Z_i+t), Section10
proves the exact full-debt ledger and its AllNever comparison. On a fixed
compact positive theta box, put K_theta=Theta_max/theta_min. The comparison
and1-nu<=beta give D_Z<=K_theta*t*beta. Substituting into(P6) yields

    k beta<=K_theta*t/M+4sqrt(C),
    beta<=K_theta*t/(M k)+(4/k)sqrt(C).               (P7)

This holds for ANY full calendar, ROOT support, cap inventory and future
owner count in this small-TOTAL-mass range. In particular C=o(beta^2)
along such minima as t->0 forces beta=O(t): eventually4sqrt(C)<=k beta/2.
If C=0, the sharper displayed constant is immediate. More generally(P6)
gives the support-free native floor D_Z>=M k beta^2 whenever C=0.
There is an explicit source dichotomy. Either

    beta<=2K_theta*t/(M k),

or4sqrt(C)>=k beta/2, so C>=k^2 beta^2/64. By(P5), the latter alternative
has a finite atom carrying TWO DISTINCT owner masses each at least
k^2 beta/192. Thus every such original global minimum has either TOTAL
mass O(t) or a pair-macroscopic burst. This uses its ORIGINAL global
ledger; it is not only a zero-native-debt tail statement.

These statements do NOT exclude the remaining beta=O(t) or dense-burst
branch or prove alpha<1.

## 10. Complete original source and no-UE-to-native access

### 10.1. Native access and exact raised correspondence

This adapter is separate from the direct native-tail theorem. No actual
positive-gap table is asserted to exist. Fix a compact positive weight
box K, write theta_min=min_(theta in K,i)theta_i>0,
Theta_max=max_(theta in K)SUM_i theta_i and Theta=SUM_i theta_i.
At t>0 raise every nonempty native reward to

    r_i(S)=theta_i[Z_i(S)+t], AllNever still zero.       (N0)

Write R for an ORIGINAL reward table, with s_i=R_i({i}). If every
original own singleton is nonpositive, AllNever is an exact
uniform equilibrium with payoff zero: a unilateral finite quit pays its
nonpositive own singleton, and live play pays zero. A hypothetical signed
Fin4 counterexample therefore has a positive own pivot s_m. The checked
full-normal-core and punishment-normal consequences named in Section15
supply punishment bounds P_i<=s_i under its no-uniform-payoff hypothesis.
Put b_m=0 and b_i=s_i otherwise. Replacing EVERY nonempty entry by
(R_i-b_i)/s_m gives pivot own one and all other owns zero. The checked
reverse uniform-payoff lift has its positive-pivot and punishment-normal
hypotheses supplied here. A uniform payoff of the normalized game would
lift to the original one. Hence the normalized game has no uniform payoff
and strictly positive original full-debt infimum. Its absorbing infimum
is positive as well.

Subtract one from EVERY nonempty entry of the pivot RECIPIENT row. Both
before and after, own singletons are nonnegative. A deterministic finite
deadline tending to infinity converges to literal Never plus its own
reward times the all-opponent-Never probability. Thus the finite-response
supremum contains Never. On ABSORBING prescribed profiles the payoff and
every finite forced response shift by the same recipient constant, so
full debts are unchanged. This produces own-zero Z with positive native
absorbing infimum A. It does not claim affine invariance of prescribed
payoffs at positive joint Never.

The positive-A region is relatively open on the own-zero affine slice.
A uniform reward change of at most epsilon changes every U and EVERY
pure response, and hence every full B, by at most epsilon. Four debts
and their absorbing infimum change by at most 8epsilon. A sufficiently
small neighborhood therefore retains A>0. No matrix, rate or clock
criterion is added to the native collision bound.

For fixed Z let M=max(1,max|Z_i(S)|), nu=product_i N_i. Move the smallest
original Never mass to any finite date. This gives a sure finite owner
and makes the profile absorbing. Its mass is at most nu^(1/4). Four
prescribed values and three other full caps change by at most
2M nu^(1/4); the mover's cap is independent of its own law. Hence

    A<=D_Z+14M nu^(1/4).                              (N1)

Native own zero implies that the finite-response supremum contains
Never. Therefore for every actual profile and its original compact lift,

    B_i^r=theta_i(B_i^Z+t),
    U_i^r=theta_i[U_i^Z+t(1-nu)],
    d_i^r=theta_i[d_i^Z+t nu].                        (N2)

Original Never, not an escaping finite mass, appears here. AllNever has
full original debt t Theta, so every original global minimum satisfies

    sum_i theta_i d_i^Z<=t Theta(1-nu)<=t Theta.

For t<theta_min A/(2 Theta_max), its native debt is less than A/2.
Equation(N1) then gives the uniform ORIGINAL collar

    nu>=(A/(28M))^4=:kappa>0, and EVERY N_i>=kappa.   (N3)

The same bounds pass to the source by exact original N convergence.
The full original infimum is positive: either native debt is at least
A/2, or (N1) forces nu>=kappa. Explicitly,

    delta_r>=min{theta_min*A/2,t*Theta*(A/(28M))^4}>0.

Consequently an original compact GLOBAL minimum exists with strictly
positive value and original Never. No lexicographic or collision selector is needed.
Every shifted own is theta_i*t>0. No quantitative minimum margin is
needed by the collision proof.


### 10.2. Original augmented carrier and independent complete laws

At a fixed table a complete private clock is implemented by its conditional
hazards q_i(n | T_i>=n), with arbitrary choices after zero-survival histories.
Conversely the only live public history is continued play, so an arbitrary
behavioral strategy determines such hazards and one complete independent
private clock. Replacing an entire marginal law averages its pure finite
and literal Never responses. Hence the full stopping-law cap equals the
unrestricted behavioral deviation cap in BOTH directions. No public signal,
correlated draw or observation of another clock is introduced.

For the native Z let H_Z be the closure of ACTUAL tuples (U^Z,B^Z,N) in
their bounded finite-dimensional box. It is compact. Its projection onto
(U^Z,B^Z) is exactly the original terminal semantic carrier: project an
actual sequence in one direction; lift it and extract the bounded N-vector
in the other. Its global continuous SUM-debt floor is therefore the ACTUAL
unrestricted debt infimum, not a new abstract-clock infimum.

The same construction at r gives H_r. On the SAME actual clock profiles,
N2 supplies a continuous transformation

    (U^Z,B^Z,N) ->
    (theta_i[U_i^Z+t(1-nu)], theta_i[B_i^Z+t], N).

Its inverse divides by the fixed positive theta_i and subtracts these
continuous N-dependent terms. Thus it maps the augmented closures onto
one another EXACTLY. Original Never coordinates, not escaping finite mass,
are used in both directions. This homeomorphism needs no collision
coordinate or lexicographic selection. Sections7--9 separately attach
the CROSS-OWNER C through its actual pair kernels.

### 10.3. Complete compiler and ALL moving response queries

Let L>=1 bound the absolute rewards at the CURRENT fixed table. Start
with actual complete-law representatives of an augmented (U,B,N) point.
At index m truncate a finite tail of total mass e_m tending to zero,
moving each removed finite draw to that same owner's literal Never.
Independent coupling changes each prescribed value and EVERY pure
finite-or-Never response by at most 2L e_m; therefore full caps have
the same error and SUM debt changes by at most 16L e_m. All original
limiting Never masses are preserved. This is finite-support approximation,
not relabeling a nonvanishing finite escaping mass as Never.

For each finite profile form the mean law mu^m=(SUM_i q_i^m)/4. Give
every occupied date its chronological raw interval of length mu^m({t})
in [0,1], and give Never the last interval. Owner i has constant density
q_i^m({t})/mu^m({t}) on that interval. These densities are in[0,4].
Coordinates are sampled independently; the chart is deterministic
bookkeeping, with no common randomization. Extract weak-star limits
f_i of the densities and a limit c_* of the finite/Never boundary.
Sequential extraction is valid because the bounded weak-star ball has
separable L1 predual.

Let E_m contain all raw interval endpoints and 0,c_m,1. Put the pure
test at the midpoint of its occupied atom interval, and at its cut if
empty. Include the final empty finite test c_m and call the finite test
set T_m. Extract Hausdorff limits E and T_*. Each component of [0,c_*]
minus E is the limit of ONE old atom interval. Its limiting owner
densities are constant, and its only test is its midpoint. Collapse
that whole component to this test. The rest of E outside T_* is null:
each component of the complement of T_* contains at most one E point.
There are countably many such components. Retain all remaining finite
cuts, and send (c_*,1) to the separate Never label.

Positive mixture atoms are isolated tests; every other finite test has
zero mixture mass. In particular the final empty finite test has no
atom. For EVERY owner,

    q_i(Never)=lim_m q_i^m(Never).                  (N4)

Testing the raw interval (c_*,1) proves (N4); replacing c_m by c_* costs
at most 4|c_m-c_*|. Reparametrize the first finite test as 0 and the last
as c, keeping the raw chart for transport. A positive ROOT law mass
therefore implies that ROOT is an isolated test.

All first-coalition indicators converge almost everywhere on the raw
product cube. Exclude only the countably many endpoints of POSITIVE
limiting atom intervals, the finite/Never boundary, and equal independent
raw coordinates. The whole endpoint limit E may have positive Lebesgue
measure and is NOT discarded. Two remaining finite
coordinates are either inside the SAME limiting atom interval, hence
in the same old atom eventually and tied, or have a limiting endpoint
strictly between them, hence are in the correct strict order eventually.
The first-coalition indicators consequently converge in L1.

Independent density products converge weak-star: first test rectangles,
then finite linear combinations, then all L1 kernels using the uniform
bound 4^4. Splitting a prescribed integral into its L1 changing-kernel
error and its fixed-kernel weak-star test proves convergence of EVERY
coalition probability and prescribed payoff. No uncontrolled products
of weak limits or exchanges of suprema and expectations are taken.

The SAME argument applies to ANY moving finite pure query. At a positive
retained atom it eventually is the midpoint of that SAME old atom; no
other old query enters a small endpoint-free neighborhood. At a nonatomic
cut its equality set has zero opponent mass, so its comparison kernels
converge almost everywhere. Never has its separate convergent kernel.
Each retained test is approached by old tests. Extracting old maximizers
gives one cap inequality, and approximating every retained test gives
the reverse. Thus ALL full caps converge to maxima over T and Never.
The response functions are continuous on T: atoms are isolated; moving
a nonatomic cut changes the payoff only on a vanishing opponent mass.
Fubini gives U_i=integral V_i dq_i. In particular zero limiting debts
make the retained laws exact Nash in this ENTIRE test menu.

The compiler supplies exact original kernels, both full-cap inequalities
and original N. Section7 additionally proves the cross-owner pair-equality
kernel limit; Section8 uses ORIGINAL conditional actual realizers. No
abstract-calendar execution, self-collision selector, five-atom refinement
or nonatomic quadrature is needed by the new quantitative consumer.

For every represented law and every owner, the exact END correction is

    V_i(c)-V_i(Never)=r_i(i) product_(l!=i)N_l>=0.      (N5)

This prices literal Never by the exact represented masses, rather than
identifying it with the empty finite END test.

For the native table all own rewards are zero, so native empty END equals
literal Never. In the positive raise they remain distinct by(N5). The new
tail argument uses NATIVE Never and the full native cap, not a positive
raised END in place of Never. The compact representation is used only to
read exact first-coalition integrals and Fubini; no actual execution on an
abstract compact time order is asserted.


## 11. The produced maximum-absorption native Nash source

Fix the own-zero native
Z with A>0, and its original augmented compact carrier H_Z of
actual(U,B,N) limits. Let E_Z be the zero-SUM-debt subset. Nonnegative
individual debts make every point of E_Z a native exact Nash semantic
point; its retained complete-clock representation is exact Nash in
the whole offered menu. AllNever belongs to E_Z, so it is nonempty
compact. Define

    alpha=min_(X in E_Z) PRODUCT_i N_i(X).

Section10.1's absorbing-completion inequality A<=D_Z+14M*nu^(1/4) gives
alpha>0. A native zero-debt point attaining alpha is PRODUCED by
compactness, not assumed to have a favorable finite realization.

For any positive theta in a fixed compact box and t>0, the exact
whole-law identities give

    D_(theta(Z+t))=SUM_i theta_i d_i^Z+t*Theta*nu.

They transfer in BOTH directions between the corresponding augmented
closures: use the SAME actual realizing profiles and their original
Never coordinates, and the exact formulas for U and B. In particular
the native alpha-minimizing Nash point supplies a raised competitor
with full debt t*Theta*alpha.

Let X_(t,theta) be ANY raised full-SUM minimum, without lex/C selection.
Writing its mapped native debts as d_i^Z>=0 gives EXACTLY

    nu_(t,theta)<=alpha,
    SUM_i theta_i d_i^Z/t
                 <=Theta*(alpha-nu_(t,theta)).         (A1)

As t->0, native debt tends to zero uniformly for theta in the compact
positive box. Every compact native limit is therefore in E_Z and has
joint Never at least alpha. Since (A1) gives the reverse inequality,

    nu_(t,theta)->alpha,
    SUM_i theta_i d_i^Z=o(t),
    delta_(t,theta)/t->Theta*alpha.                   (A2)

The first two statements are uniform over ALL minima and theta in
the box: a failing sequence would have a convergent augmented native
subsequence contradicting the preceding compact-limit argument. The
last statement has the natural varying Theta factor. No native
collision-maximizing selection, individual debt equality among positive minima or minimizing
suffix is inherited.

Thus alpha=1 would force TOTAL finite mass to vanish at every raised
minimum, for ALL future counts. Alpha<1 produces a native exact Nash
limit with MAXIMAL absorption among the WHOLE native Nash carrier.
Closing that macroscopic minimum-Never Nash class is a concrete missing
global step. A regular ROOT Nash point or an arbitrary native Nash law
is not automatically the produced alpha-minimizer. No continuation to
lower nu, absorbing profile or UE is proved by this observation.

The collar and Section10.3 give a faithful retained native Nash
representation of every alpha-limit. Pair transport and the ACTUAL
conditional-source proof in Sections7--8 apply to ANY such representation.
Every nontrivial sufficiently small conditional tail then obeys(P4)--(P5).
This is a concrete surviving-tail restriction of the PRODUCED native source,
not an assumed exact-Nash actual realizer. No statement that alpha<1 or
that all source mass is small is needed for that tail conclusion.

## 12. Complete exact-Nash control: serialization has born-query error O(e)

For masks1,...,15, with mask(S)=SUM_(i in S)2^i, give ALL sixty entries by

    Z_0=[0,0,1,0,-1,0,0,0,0,0,0,0,0,0,0],
    Z_1=[0,0,-1,0,0,1,0,0,0,0,0,0,0,0,0],
    Z_2=[0,0,0,0,1,-1,0,0,0,0,0,0,0,0,0],
    Z_3=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0].          (Q1)

All passive rewards and own singletons are zero; the only nonzero entries
are the antisymmetric participant pairs on {0,1,2}. Fix0<e<1/64. Owners
0,1,2 put mass e at actual date0 and1-e at Never. Owner3 puts sqrt(e) at
date1 and1-sqrt(e) at Never. Every original N_i>0 and

    beta=3e+sqrt(e)<1/2, C=3e^2.

For each i in{0,1,2}, its date0 forced response has the two opposite pair
rewards with equal probability e(1-e), so pays zero. Both opponents
quitting gives triple zero. Its date1 query either follows passive zero
or meets only owner3 with pair zero. Every later finite and Never response
also pays zero. Row3 is identically zero. Thus ALL old finite/Never
responses and prescribed values are zero: U=B=0,D=0.

Serialize the three root atoms in ANY order, keeping owner3's atom later
and all masses fixed. Every prescribed first exit is now a singleton,
so every prescribed payoff is zero. If j is the first serialized owner,
some i!=j has J_ij=1. Its forced reply at that FIRST new date pays e.
Hence D_new>=e for EVERY serialization order, although

    C/beta^2=3e/(1+3sqrt(e))^2->0,
    D_new/beta^2>=1/(1+3sqrt(e))^2->1,
    D_new/C>=1/(3e)->infinity.                        (Q2)

This is a FULL-query countertest to pricing born caps by O(C). It does
not refute the present theorem: every prescribed conditional continuation
of the serialized law is zero, so its separate positive-own charge T_R
is zero. Treating that charge and the current-query debt separately is
essential. The literal AllQuit profile is absorbing exact Nash, with all
grand and passive triple rewards zero. Thus A=0 honestly.

## 13. A signed hybrid control with BOTH edits and positive own charge

Define another complete sixty-entry native table. For nonempty S write
m(S)=SUM_(j in S)2^j and let rem17 denote the least nonnegative residue.
Use the disjoint rules

    Z_i({i})=0;
    Z_i(S)=100 if |S|>=3 and i in S;
    Z_i(S)=1 if |S|>=3 and i notin S;
    Z_i(S)=rem17((i+1)m(S)^2+3m(S)-7i)-8 otherwise.  (Q3)

Here M=100 is a bound. AllQuit is strict absorbing Nash, paying100
against withdrawal one; A=0 honestly. The following non-Nash test uses
triple counterfactual replies as well as signed singleton/pair entries.
Old marginal atoms are

    date0: p_0=1/10, p_1=1/1000;
    date1: p_2=1/100, p_3=1/1000;
    all remaining mass is the SAME owner's Never.

Then beta=14/125,C=11/100000. At epsilon=1/50 the first shared block is
BIG and the second SMALL. Delete owner1's date0 minority, E=1/1000,
keep owner0 whole, and serialize the small block as owners2 then3.
Thus C_s=1/100000 and R has three singleton occupied dates. The optimal
cutoff2sqrt(C) induces the SAME two classes. The theorem's r lies below
one: explicitly

    r=552695513/1254400000+sqrt(110)/28
                                  <1/2+11/28<1.

All complete pure menus can be checked by independent first-coalition
enumeration. The following display gives EVERY nonduplicate finite query,
with its LAST column the common empty END and literal Never value.
For the old clock the columns are0,1,END:

    V_0=(-7/1000,-118369/6250000,337687/12500000),
    V_1=(-1/2,758491/1000000,655963/1000000),
    V_2=(59/5000,248991/2500000,1022937/10000000),
    V_3=(-481/5000,-92189/200000,-67733/125000).

    U=(2951683/125000000,654807037/1000000000,
                         102266727/1000000000,-541783081/1000000000),
    B=(337687/12500000,758491/1000000,1022937/10000000,-481/5000),
    D=552695513/1000000000.

For the hybrid R the columns are0,1,2,END:

    V_0=(0,-1/50,1401/50000,501/20000),
    V_1=(-1/2,763/1000,324827/500000,655891/1000000),
    V_2=(0,1/10,259/2500,1063/10000),
    V_3=(-1/10,-91/200,-67/125,-67/125).

    U_R=(4509/200000,655891/1000000,106237/1000000,-67/125),
    B_R=(1401/50000,763/1000,1063/10000,-1/10),
    D_R=548647/1000000, nu_R=890109/1000000,
    T_R=321/125000>0.

For delta=1/2, lambda=500000/109891, the new hazards are

    q'=(50000/109891,4500/59891,891/110782).

The dilated R' has the SAME four query types0,1,2,END, with

    V'_0=(0,-9000/59891,12609/59891,22545/119782),
    V'_1=(-250000/109891,381500/109891,324827/109891,655891/219782),
    V'_2=(0,50000/109891,2876275762/6086972381,844662881/1739134966),
    V'_3=(-50000/109891,-227500/109891,-268000/109891,-268000/109891).

    U'=(22545/219782,655891/219782,106237/219782,-268000/109891)
       =lambda U_R,
    B'=(12609/59891,381500/109891,844662881/1739134966,-50000/109891),
    D'=134436633185603/52079266124353.

These44 distinct menu entries include every natural deadline and Never,
because post-LAST finite replies all have the displayed END kernel.
They verify(6),(8),(9),(10) and strict debt amplification after dilation,
not debt invariance. This is not a global minimum or a positive-A game.

The removed owner1 has no later finite atom in this particular fixture.
Past censoring still needs its denominator charge in the GENERAL proof.
For an exact marginal stress, a law with mass e at date0 and f at date2
has conditional future mass f/(1-e) after0; moving its PAST atom e to
Never changes that conditional mass to f. At e=1/1000,f=1/100 the
variation is1/99900>0. Thus past removal cannot be ignored merely
because the target current atom lies later; the4E bound covers it.

## 14. Dense shared bursts remain an honest boundary

For EVERY nonempty S specify a third full sixty-entry table by

    Z_i(S)=1 if i notin S;
    Z_i(S)=2 if i in S and |S| is even;
    Z_i(S)=0 if i in S and |S| is odd.

Own singletons are zero. Let every owner have actual atoms
q_i(n)=b*2^(-n-1) for n>=0 and Never1-b, with0<b<1/8.
Conditional remaining finite probability f has current conditional
atom f/2. A forced current query pays2 times the odd-parity probability
of three independent coins of rate f/2, namely1-(1-f)^3, EXACTLY the
conditional Never value. Earlier opponent absorption pays one for both.
Thus EVERY finite/Never response and prescribed value equals
1-(1-b)^3, and the profile is full native Nash with positive original N.

Here beta=4b and C=6*SUM_n b^2*4^(-n-1)=2b^2, so

    C/beta^2=1/8.

The ratio does NOT vanish in late conditional tails; they retain dense
shared bursts. AllQuit is absorbing Nash, paying two against withdrawal
one, so A=0 honestly. This tests the collision-density boundary rather
than asserting such a source has positive absorbing gap.

## 15. Exact implementation overlap, source correspondence and handoff

Complete-law payoff and cap meanings in BOTH directions are
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff`,
`quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`,
`quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
and `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
(`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`).
Thus every law-replacement cap used here is the unrestricted behavioral
cap. The delayed-finite/Never theorem is
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile`
(`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`),
with zero own singleton; Section5 also proves its direct actual-law limit.

The original carrier and sequential access are
`quittingTerminalSemanticCarrier` and
`exists_terminalProfile_sequence_tendsto_semanticPair`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`). The SUM
functional is `quittingTerminalSemanticDebtSum`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticDebt.lean`). Its actual
infimum equals every global original minimum by
`quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum`, and
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`) applies to
the original/normalized no-UE game. It is NOT applied to native Z merely
from positive ABSORBING gap: own-zero native Z has the AllNever payoff.

Native access uses
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`),
`all_punishmentNormal_of_normalCore_eq_univ`
(`UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean`),
`quittingSoloReward_singlePivotNormalized`
(`UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean`) and
`isUniformEquilibriumPayoff_original_of_singlePivotNormalized`
(`UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean`).
Their finite-player, positive-pivot and punishment-normal assumptions are
supplied in Section10.1. The absorbing row-constant shift is distinguished
from an invalid unconditional translation on defective prescribed laws.

The existing `QuittingConditionedDiffuseCertificate` and
`quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarilyFineConditionedDiffuseCertificates`
(`UniformEquilibrium/Quitting/Cycles/ConditionedDiffuseUniform.lean`)
package a supplied exact conditioned chronology, singleton-tight boundary,
mesh bounds and DELETED-COMPLETE opponent-clock divergence. The implemented
`conditionedDiffuseRescaledRoots_isεAsymptoticNash_and_approximates`
(`UniformEquilibrium/Quitting/Cycles/ConditionedDiffuseCompiler.lean`)
uses these hypotheses to get playerwise opponent survival tending to zero
and a target approximate Nash profile. Those hypotheses are preserved in
the comparison; none is silently asserted for the present arbitrary input.

The new actual theorem instead starts from ANY complete-law profile and
pays its ORIGINAL full debt. It deletes minority atoms at large shared
dates, serializes only fine shared dates and prices ALL born queries by
TWO separate quantities. The output before final completion has positive
Never at every owner; its opponent survival does not need to vanish.
The exact deleted-own sum(9), the explicit delta floor and the final
single-owner completion replace such a transversality assumption. No
conditioned clock certificate or strategic selector remains unproduced.
The product-preserving singleton part is elementary independent hazard
reconstruction, not a claim that exact rescaling works on shared stages.

For formalization, first add the original-N augmented carrier and its exact
native/raised homeomorphism, and prove the mean-law compiler's BOTH cap
inequalities and full Fubini identity. Extend that compiler by the finite
CROSS-OWNER equality kernel in(P1); do not substitute a same-owner square,
weak measure continuity or a collision-maximizing source selection.

Then formalize the ACTUAL hybrid operations, keeping original full caps in
identity(2) and the supported-atom test(3). The old g_i charges are paid by
ORIGINAL debt, while conditional changes include PAST removed atoms and
normalizing denominators. Bound every new finite query, literal Never and
mixed response; positive own continuations require their SEPARATE weighted
charge. Formalize the deleted-own identity(9) before using its coefficient
bounds; do not assert an unrestricted one-stage-deviation principle.

For retained suffixes, use matching ORIGINAL actual cut realizers and
prove(P3). At a positive retained atom condition at the LEFT raw boundary
and include the WHOLE old atom. Keep ORIGINAL Never positive in the limit.
The conditional pair kernel and debt limits then give(P4), the two-owner
burst and the original global-minimum scale(P7). No abstract conditional
calendar is assumed executable, and no suffix minimum is inherited.

All complete-table controls have explicit absorbing Nash profiles and
honest A=0. The packet excludes vanishing relative cross-owner collision
and quantifies the actual surviving bursts; it does not exclude dense
bursts, finite macroscopic LAST, beta=O(t), alpha=1, arbitrary nonvanishing
native mass or all four-player counterexamples. This is ordinary
mathematics to be formalized, not a new checked Lean result or a build.
