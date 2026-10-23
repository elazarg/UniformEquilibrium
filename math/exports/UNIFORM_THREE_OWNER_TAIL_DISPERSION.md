# Uniform three-owner tail dispersion

This is an ordinary mathematical proof; no new Lean declaration is claimed.
The result excludes concentration on two owners after normalization by TOTAL
finite mass, including when that total tends to zero. It applies to the
original full-debt carrier and its raised global minima. It does not produce
an absorbing profile in the surviving three- or four-owner stratum.

## 1. Data, quantifiers, and theorem

There are four players. The fixed native reward table Z has own singleton,
live, and literal AllNever rewards zero. Fix M>0 with |Z_i(S)|<=M for every
recipient and nonempty coalition. Each player privately and independently
draws a complete clock on Nat plus a separate Never label. A deviation
replaces its ENTIRE law. Thus all finite deadlines, Never, and arbitrary
private mixtures are included.

For an actual profile P, write U_i for prescribed terminal payoff, B_i for
the full response supremum, d_i=B_i-U_i>=0, D=sum_i d_i, N_i for original
Never mass, and f_i=1-N_i for TOTAL finite mass, including date zero. Put

    beta=sum_i f_i,
    f_(1)>=f_(2)>=f_(3)>=f_(4),
    epsilon=f_(3)+f_(4).

Let A be the infimum of D over ALL actual almost surely absorbing profiles.
Assume A>0, every recipient row has distinct entries, and for each pair u,v,

    Gamma_uv J_vu-Gamma_vu J_uv != 0,
    Gamma_uv=Z_u({v}),  J_uv=Z_u({u,v}).                 (1)

J is the raw pair reward. Row distinctness implies Gamma_uv!=0 and
J_uv!=Gamma_uv. No calendar bound, finite-support assumption, minimum
selection, or supplied Never collar is imposed on P.

**Uniform dispersion theorem.** There is c=c(Z)>0 such that EVERY actual
profile satisfies

    D + beta epsilon >= c beta^2.                      (2)

The constant is qualitative. One may decrease it without affecting any
conclusion. Equation (2) also holds on the original augmented closure H_Z
of actual tuples (U,B,N), since its two sides are continuous functions of
those coordinates. This passage does not execute an abstract clock.

In particular, at any nontrivial zero-debt point of H_Z,

    epsilon>=c beta,       f_(3)>=c beta/2.             (3)

Thus at least three owners carry comparable TOTAL finite mass. The theorem
does not assert a common three-owner atom or comparable mass at each date.

## 2. Elementary coupling, completion, and one-owner scaling

If selected finite masses of total e are moved to the SAME owners' Never
labels, couple all other draws identically. Each of four prescribed values
changes by at most 2Me. For recipient i, every response and hence its full
cap changes by at most 2M times the removed OPPONENT mass. Each removed
owner is an opponent of exactly three recipients. Consequently

    |D_new-D_old|<=8Me+6Me=14Me.                       (5)

The finer bound for each recipient will also be used: the change in a
query-minus-Never gap, or in cap minus a fixed mixed response, is at most
4Me. These bounds are uniform over the full replacement menu.

For one finite owner h with mass f, normalize its finite part to a sure
finite law on the SAME dates. The owner's payoff and cap are zero. Every
observer's prescribed and response payoffs scale by 1/f, because its own
singleton payoff on the removed Never branch is zero. Taking the full
supremum preserves this scaling. The normalized profile absorbs, so

    D_one>=Af.                                        (6)

The f=0 case is immediate; no assumption on signs is needed.

There is also a Never collar at small debt. Move the smallest marginal
Never mass e to a finite date. The modified profile absorbs and the same
coupling count gives A<=D+14Me. Since e<=nu^(1/4), where nu=product_i N_i,

    A<=D+14M nu^(1/4).

Consequently D<A/2 implies every N_i>=nu>=(A/(28M))^4=:eta>0.
A sure solo profile has own debt zero and three observer debts at most
2M, so A<=6M and eta<1. This collar depends only on the table.

## 3. Reduction of a failed dispersion bound

Suppose (2) fails. There is a sequence of actual profiles with beta>0 and

    D/beta^2 -> 0,          epsilon/beta -> 0.          (7)

The beta=0 profile cannot witness failure. Extract fixed labels for the
ordered masses. Since beta<=4, D->0 and epsilon->0.

Censor every owner except the largest. Equations (5)--(6) give

    A f_1 <= D+14M(f_2+epsilon).

Since f_1=beta-f_2-epsilon,

    f_2/beta >= A/(A+14M)-epsilon/beta
                            -D/[(A+14M)beta].         (8)

Hence both f_1 and f_2 are bounded below by a fixed positive multiple of
beta. Pass to f_2/f_1->lambda in (0,1]. If beta stayed bounded below,
censor owners 3 and 4. Their mass tends to zero, so (5) gives pair debt
tending to zero. Both remaining finite masses stay bounded below and the
completion bound above gives a fixed original Never collar. The
compact-clock argument and collared pair exclusion proved in Section 5
rule out exactly this sequence. Therefore beta->0. In particular,

    D/(f_1 f_2)->0,
    epsilon/f_i->0 for i=1,2,    N_i->1 for all i.     (9)

No externally supplied Never collar is used. If desired, reduce to finite
supports now: move a total finite tail e_n=o(beta_n^2) to its original
Never labels. Formula (5) preserves (7); relative leading-mass errors
vanish, and relabeling on a subsequence preserves (8)--(9). Every actual
law admits such a cutoff, without a common bound on support size. Reset
the notation to this finite-support sequence. This operation never
identifies escaping finite mass with Never in the later compact limit.

## 4. The normalized active response estimate

Let W_i be the original response payoff from pure Never. If f_i>0, let
P_i be the response payoff averaged under i's own normalized finite law.
Fubini gives the exact decomposition

    d_i=N_i(B_i-W_i)+f_i(B_i-P_i).                     (10)

Both summands are nonnegative. Therefore, eventually N_i>=1/2 and

    0<=B_i-W_i<=D/N_i,
    0<=B_i-P_i<=D/f_i.                                (11)

The first bound also holds when f_i=0: then U_i=W_i and d_i=B_i-W_i.
Thus it applies to outsiders with no finite mass as well.

Keep owners 1 and 2 unchanged and censor owners 3 and 4 to Never; call
this pair profile Q. Write F_i for the normalized finite law of active
owner i. For {i,j}={1,2}, let b_i be i's full cap against the SURE finite
law F_j, all other opponents Never, and let p_i be the average response
under F_i against that same opponent law. The corresponding Never value
is Gamma_ij. Own-singleton zero gives the exact scaling identities

    B_i(Q)=f_j b_i,
    W_i(Q)=f_j Gamma_ij,
    P_i(Q)=f_j p_i.                                   (12)

Here P_i(Q) is the conditional finite response average, not the
unconditional prescribed payoff. By (11), uniform gap transfer (5), and
the fact that every such response is bounded by its cap,

    0<=b_i-Gamma_ij<=D/(N_i f_j)+4M epsilon/f_j,
    0<=b_i-p_i<=D/(f_i f_j)+4M epsilon/f_j.            (13)

All right sides tend to zero by (9). Thus

    b_i->Gamma_ij,       p_i->Gamma_ij                 (14)

for BOTH active owners. This is the essential improvement over merely
bounding the pair profile's TOTAL debt by D+14M epsilon. Division by the
other owner's mass is harmless because the two leading masses are
comparable to beta and epsilon=o(beta).

## 5. One common compact clock and the exact geometric pair

### 5.1. Bounded independent charts and retained tests

The following compactness construction applies to any actual sequence at
the fixed bounded table. First truncate finite tails with total mass
e_n->0 to the original Never labels; (5) and its uniform response bound
preserve all limiting prescribed values, caps, and Never masses. At each
finite-support index let mu^n be the average of the four complete laws.
Partition [0,1] into chronological intervals of lengths mu^n({a}), one
for each occupied finite date and a last interval for Never. Ignore empty
intervals. On a's interval set w_i^n=P_i^n({a})/mu^n({a}). Thus
0<=w_i^n<=4, sum_i w_i^n=4 almost everywhere, and integral w_i^n=1.
Sampling the four densities independently preserves independence; the
chart is deterministic bookkeeping, not a common random signal.

Pass to weak-* limits w_i on a common subsequence. Sequential extraction
is valid because L1[0,1] is separable. Let c_n be the finite/Never boundary
and extract c_n->c. Let E_n contain all interval endpoints, including
0,c_n,1. Map every finite query t to
mu^n({a:a<t})+mu^n({t})/2; an occupied date maps to its midpoint and an
empty date to its cut. All dates after the last occupied finite date map
to c_n. Let T_n be this finite set of distinct query locations. Extract
Hausdorff limits E_n->E and T_n->T. Then T is contained in [0,c], c is
in T, and 0,c,1 belong to E. Literal Never is kept as a separate label.

Each component J=(a,b) of [0,c] minus E is the limit of ONE old atom
interval: a compact subinterval of J eventually has no old endpoint,
and the Hausdorff endpoint convergence forces the endpoints of that old
interval to a,b. The only retained query in J is its midpoint. Each w_i
is constant almost everywhere on J by testing any two interior compact
subintervals. The same argument applies to the Never interval (c,1).

The set (E intersect [0,c]) minus T is null. Indeed each component of
the complement of T contains at most one E point: two such points would
force an old atom midpoint between approximating endpoints and hence a
retained test there. There are only countably many components. Collapse
each J to its midpoint, keep the remaining finite points of E intersect T,
and send (c,1) to the separate Never label. Map the exceptional null set
arbitrarily. Push each w_i dx forward under this common map. The resulting
independent laws live on X=T disjoint-union {Never}. Their positive finite
mixture atoms are isolated midpoints; all other finite points have zero
mixture mass. In particular the final finite test c has no atom.

Literal Never is preserved: its old mass is integral_(c_n,1) w_i^n;
changing c_n to c costs at most 4|c_n-c|, and weak-* convergence tests
the fixed indicator of (c,1). Hence each retained Never mass is its
original limiting Never mass, and finite mass is also preserved.

### 5.2. Every coalition, moving response, and full cap converges

The first-coalition indicator kernels on independent raw coordinates
converge almost everywhere. Exclude the countably many endpoints of
positive retained intervals, the finite/Never cut, and equal raw
coordinates. Do NOT discard the full endpoint set E, which may have
positive measure. Two remaining finite coordinates either lie in one
retained atom interval and eventually tie in one old atom, or have a
retained endpoint strictly between them and eventually occur in the
correct strict order. Never classification also stabilizes. This proves
almost-everywhere, hence L1, convergence of all coalition kernels.

Independent density products converge weak-* on each raw product cube:
first test rectangles, whose integrals factor into convergent marginal
integrals, then use density of rectangular step functions in L1 and the
uniform product bound 4^4. Split each changing-kernel integral into its
L1 kernel error times a bounded density product and its fixed limiting
kernel tested against the weak-* density product. Thus prescribed
coalition probabilities and payoffs converge exactly.

For ANY moving sequence of pure queries with locations x_n->x in T,
response kernels converge as well. At an isolated midpoint, the old query
eventually is the midpoint of its very same old atom interval, so ties
are preserved. At any other retained test the limiting opponent atom
mass is zero; comparison kernels converge away from a null equality set.
The same bounded-density integral argument works. Never has its separate
convergent kernel. The response function on T is continuous: isolation
handles atoms, and moving a nonatom query changes its value only on a
vanishing opponent mass. Never is isolated in X.

Every retained test has actual moving witnesses by Hausdorff convergence.
Extracting old maximizing tests gives the upper cap inequality; using
witnesses for any retained test gives the reverse. Thus old full caps
converge to maxima over X. Boundedness, independence, and the Borel
order/tie kernels give retained Fubini: U_i=integral_X V_i dq_i. If debts
tend to zero, the limiting own law is concentrated almost everywhere
on full-cap responses and is exact Nash against the entire retained menu.

The same convergence holds for unary response kernels after replacing one
opponent by Never in the kernel: the unchanged raw coordinate has exactly
the same comparison/tie analysis and is integrated against its bounded
own density. Thus all solo comparisons can be retained on the SAME chart.
No separate compactifications of solo subprofiles are used.

### 5.3. Active Never contact forces a common geometric calendar

Consider a retained pair with positive finite masses a_1,a_2 and all other
players Never, whose active prescribed values and full caps equal their
Never values Gamma_ij a_j. Zero prescribed Never is allowed. Put
mu_i(x)=q_i({x}) and let R_i(x) be its inclusive finite tail. The finite
query payoff is Gamma_ij(a_j-R_j(x))+J_ij mu_j(x). Fubini contact gives

    J_ij mu_j(x)=Gamma_ij R_j(x)                       (16)

for q_i-almost every finite x. If C is the common finite tie probability
and A_ij is the probability i<j<Never,
integration gives

    J_ij C=Gamma_ij(A_ij+C).

Since A_12+A_21+C=a_1 a_2>0 and both Gamma values are nonzero, C>0. Independence
then supplies a common atom. At each common atom (16) holds pointwise,
so the fixed ratios

    z_j=Gamma_ij/J_ij=mu_j(x)/R_j(x)

belong to (0,1); zero is impossible, and one is excluded by row
distinctness. In particular the denominators J_ij are nonzero. Write
rho_i=1-z_i in (0,1).

Every common atom x has only finitely many common predecessors: if it
has k of them then 0<R_i(x)<=a_i rho_i^k. Thus there is a first common atom.
Integration of (16) before it has zero tie integral and positive opponent
tail, excluding all earlier own mass. Repeat on strict tails; those
remain positive since z_i<1. This gives successive common atoms tau_m
and excludes all intervening mass. The residual tails tend to zero, so
the ENTIRE finite parts are

    q_i({tau_m})=a_i z_i rho_i^m,   m=0,1,... .         (17)

This argument also excludes any diffuse residual. Every tau_m is an
old retained query. The pair guard (1) implies z_1!=z_2 and hence
rho_1!=rho_2.

### 5.4. Collared pair exclusion and the normalized application

There is no retained exact Nash pair with both finite masses a_i>0 and
both Never masses n_i=1-a_i>0. Fubini makes Never a full maximizer because
it has positive prescribed mass. Apply the geometric result above. If
s is the slower owner and w the faster, an outsider h's Never-minus-tau_m
response gap is exactly

    a_s n_w rho_s^m(Gamma_hs-z_s J_hs)
      +a_w n_s rho_w^m(Gamma_hw-z_w J_hw)
      +a_s a_w(rho_s rho_w)^m C_h,

where C_h is the bounded Never-minus-first-query difference against both
sure geometric conditional laws. This follows by discarding outcomes
before tau_m and separating the remaining one-finite and two-finite
branches. The expression is nonnegative by Nash. Since a_s n_w>0,
divide by rho_s^m and send m to infinity. Both outsiders obey
z_s J_hs<=Gamma_hs, while active w obeys equality from (16). The sure
geometric solo construction spelled out in Section 6 is then absorbing
exact Nash, contradicting A>0.

This proves the sequence exclusion used in Section 3: compactify its
censored pair profiles by Sections 5.1--5.2. Their limits have both
finite masses positive, positive Never masses, and zero debt. The preceding
paragraph excludes that limit. No quantitative two-owner floor is used.

For the SMALL-beta argument, instead compactify the sure conditional
laws F_1,F_2 from Section 4, with other players Never, retaining the unary
kernels on the same chart. Equation (14) gives limiting prescribed,
cap, and Never values all equal to Gamma_ij. Thus Section 5.3 applies
with a_1=a_2=1, producing (17) with those masses. This establishes the
normalized geometric pair used below without assuming prescribed Never
has positive mass in that pair.

## 6. Every outsider query and the absorbing contradiction

Fix either outsider h in {3,4}. It need not have been prescribed Never
in the original profile. Nevertheless (11) implies, for EVERY response x,

    W_h(P)-V_h(P,x)>=-D/N_h.

The uniform gap transfer after censoring gives

    W_h(Q)-V_h(Q,x)>=-D/N_h-4M epsilon.               (18)

On the common normalized chart, let Q_hi(x) be h's response payoff
against the sure conditional law F_i alone, and put
A_hi(x)=Gamma_hi-Q_hi(x). Let W_h12 be its Never payoff against both
sure conditionals, and Q_h12(x) its response payoff against both.
Splitting Q according to the two finite/Never indicators gives the
exact identity, with f=f_1 and g=f_2,

    W_h(Q)-V_h(Q,x)
      =f A_h1(x)+g A_h2(x)+fg R_h(x),                 (19)
    R_h(x)=W_h12-Gamma_h1-Gamma_h2
                      -Q_h12(x)+Q_h1(x)+Q_h2(x),
    |R_h(x)|<=6M.

These are identities at each sequence index. Divide (18)--(19) by f.
The error (D/N_h+4M epsilon)/f tends to zero, gR_h tends to zero
uniformly, and g/f->lambda>0. The same-chart unary convergence at ANY
retained test and its actual moving witnesses therefore gives

    A_h1(x)+lambda A_h2(x)>=0.                        (20)

Both outsiders obey (20), including at EVERY tau_m of (17). At those
queries,

    A_hi(tau_m)=rho_i^m(Gamma_hi-z_i J_hi).            (21)

Let s be the slower of the two geometric owners, rho_s>rho_w. Its
coefficient in (20) is strictly positive, whether it is 1 or lambda.
Divide by rho_s^m and let m increase. Thus BOTH outsiders satisfy

    z_s J_hs<=Gamma_hs.                               (22)

The other active owner w satisfies equality z_s J_ws=Gamma_ws by (16).

Now construct an ACTUAL profile on Nat: only s uses the sure geometric
law with hazard z_s from date zero; all other owners use Never. The
owner s has value and cap zero. Every observer h has prescribed payoff
Gamma_hs, and its date-m response is

    Gamma_hs+rho_s^m(z_s J_hs-Gamma_hs)<=Gamma_hs.

Never gives equality, and private mixtures cannot improve. This is an
absorbing exact full Nash profile, contradicting A>0. It uses an actual
integer calendar and no invented intermediate query. This contradiction
proves (2), including all mass and calendar limits. There are only finitely
many possible leading pairs, already fixed by subsequence extraction.

## 7. Original raised global minima

Fix positive weights theta_i, put Theta=sum_i theta_i and
K=Theta/min_i theta_i, and raise every nonempty reward to
r_i(S)=theta_i[Z_i(S)+t], t>0, leaving AllNever zero.
For a native table, a deadline tending to infinity has payoff tending to
the Never payoff: on the opponent-Never event the own singleton is zero.
Thus the supremum of finite response payoffs already includes Never.
Every forced finite response guarantees absorption and gains exactly t
under the raise. A raised Never response is no larger than the native
Never response plus t. Consequently the exact identities are

    B_i^r=theta_i(B_i^Z+t),
    U_i^r=theta_i[U_i^Z+t(1-nu)],
    d_i^r=theta_i[d_i^Z+t nu].

They hold on actual profiles and pass continuously to H_Z. Its projection
to (U,B) is the closure of the original prescribed/full-cap pairs: lift
an actual realizing sequence and extract its bounded Never vector for
one direction; projection gives the other. Thus global minimization of
the displayed full SUM debt over H_Z is the original minimization.
AllNever is an actual competitor of raised debt t Theta. At EVERY original
raised global SUM minimum, comparison therefore gives

    sum_i theta_i d_i^Z<=t Theta(1-nu),
    D_Z<=Kt beta.                                     (23)

These are original full-debt minima, not finite-menu Nash solutions.
Combining (2) and (23), for beta>0,

    epsilon>=c beta-Kt.                               (24)

Hence every such minimum satisfies

    beta<=(2K/c)t,   OR   f_(3)>=c beta/4.             (25)

The beta=0 case belongs to the first branch. In particular beta/t->infinity
forces liminf f_(3)/beta>=c/2 by (24), not merely positivity of a third
coordinate. The weaker c/4 bound in (25) is a convenient uniform dichotomy.
Weights in a fixed compact positive box admit a uniform K.

For a native zero-debt minimum of joint Never at alpha in (0,1),
beta>=1-alpha, so (3) gives f_(3)>=c(1-alpha)/2. For alpha=1, Section 10
gives beta_t->0; (25) excludes all normalized one- or two-owner
concentration in the branch beta_t/t->infinity. The beta=O(t) branch,
interior co-maximizers, and laminar leaf consumption remain unresolved.

## 8. Moving survival cuts, including microscopic native tails

For an actual profile with each original N_i>=kappa>0, take any old
whole-date cut, including an empty prefix. Let R_i be its unnormalized
finite mass strictly after the cut, S_i=R_i+N_i its survival mass, and
R=sum_i R_i. The conditional independent tail Q has

    f_i(Q)=R_i/S_i,
    R<=beta_Q<=R/kappa,
    D(Q)<=D(P)/product_i S_i<=D(P)/kappa^4.            (26)

Here is the debt transport proof. For a pure suffix response x, including
Never, the original response is a fixed payoff a_i from opponent exits
in the deleted prefix plus H_i V_i^Q(x), where H_i=product_(j!=i)S_j.
Hence B_i(P)>=a_i+H_i B_i(Q). Fubini expresses d_i(P) as the integral
of nonnegative cap gaps. Keep only the own suffix draws, of mass S_i,
and apply that inequality. This gives d_i(P)>=S_i H_i d_i(Q) and hence
(26). No suffix minimum is inferred.
If R_(3) is the third largest UNNORMALIZED R_i, choosing the two largest
R_i as a candidate pair to retain gives

    epsilon_Q<= [R_(3)+R_(4)]/kappa<=2R_(3)/kappa.     (27)

The ordering of conditional masses need not coincide with that of R_i;
epsilon_Q is the minimum removed mass over all choices of two kept owners.
For R>0, (2), (26), and (27) imply

    R_(3)>=kappa c R/2-D(P)/(2 kappa^3 R),
    2R_(3)R+D(P)/kappa^3>=kappa c R^2.               (28)

The corresponding inequality at R=0 is trivial.

For an exact native zero-debt retained source with a positive Never
collar, use the raw chart of Section 5.1 and take a whole cut at a point
a of E, at or before c. Choose old whole-atom endpoints a_n in E_n
tending to a. At a=c choose exactly a_n=c_n, so old Never draws are
never included in the removed prefix. The suffix-region indicators
converge in L1, since their discrepancies lie between a_n and a and
between c_n and c. Bounded densities and weak-* testing of the fixed
limiting indicator show convergence of every unnormalized finite suffix
mass. Never converges separately. Each old cut is the last included
occupied date, allowing an empty prefix. Apply (28) to the realizers with
any 0<kappa'<kappa, which is an eventual collar, pass to the limit at
EACH fixed cut, then let kappa' increase to kappa. Every nonempty suffix obeys

    R_(3)>=kappa c R/2,                               (29)

uniformly even as R tends to zero along later whole cuts. No atom is
sliced internally, no unqueried deadline is added, and original Never
mass remains separate. Alternatively its conditional tail is a zero-debt
point of H_Z and (3) applies. Conditioning need not preserve the global
minimum-Never selection; neither proof uses that property.

For APPROXIMATE moving cuts, D(P)->0 alone is insufficient if R->0.
Equation (28) gives a positive limiting third-tail fraction when
D(P)=o(R^2), or more intrinsically D(Q)=o(beta_Q^2). Under only the
raised global source bound (23), the sufficient comparison is
R^2 >> t beta_full, with K and the Never collar controlled. An exact-menu
conditional source that separately has D(Q)<=t beta_Q has the different
sufficient condition beta_Q/t->infinity. That additional menu estimate
is not silently supplied to original global minima.

## 9. Every exact finite-menu equilibrium at a small offset

Let s_i>=0 with sum_i s_i=t, and add s_i to every nonempty recipient-i
reward. Fix ANY finite menu consisting of dates 0,...,T and literal Never,
and ANY exact Nash profile in this menu. It is an actual complete-law
profile. Such profiles exist for every deadline and offset allocation by
the mixed Nash existence theorem for finite games; each marginal mixed
action is exactly one independent complete clock. Write
H_i=product_(j!=i)N_j, and W_i for its native Never response.
Native responses after T equal W_i, so its full native cap is already
the maximum over the finite menu. A finite menu response gains s_i,
whereas Never gains s_i(1-H_i). If C_i is the raised menu cap, then

    B_i^Z<=C_i-s_i(1-H_i),
    U_i^Z=C_i-s_i(1-nu),
    d_i^Z<=s_i(H_i-nu)=s_i f_i H_i.                  (30)

Thus D_Z<=sum_i s_i f_i H_i<=t beta and also D_Z<=t. If t<A, the
profile cannot absorb, since absorbing debt is at least A. Independence
then implies EVERY N_i>0. Its prescribed Never action is a raised menu
maximizer. For any offered finite response x this gives

    V_i^Z(x)+s_i<=W_i+s_i(1-H_i),
    V_i^Z(x)<=W_i-s_i H_i<=W_i.

It follows that the full native cap is precisely W_i, and (30) is now
the exact identity

    d_i^Z=s_i f_i H_i.                               (31)

Every supported finite action has native loss W_i-V_i^Z(x)=s_i H_i.
Therefore EVERY such menu equilibrium satisfies (24)--(25) with K=1.
This conclusion is independent of the deadline, offset allocation, and
selection among menu equilibria. It remains a support restriction rather
than an absorbing-profile producer.

The same statement holds for each nonempty conditional menu tail: the
original positive Never masses give positive survival. Against opponents
conditioned to survive the cut, all old suffix comparisons have the same
positive opponent-survival multiplier and the same cancelled prefix term.
Every supported conditional action remains a maximizer, and Never remains
in the suffix menu. Thus the conditional profile is exact menu Nash with
the SAME offsets; (31) applies with its conditional masses. If its
beta_Q/t tends to infinity, its third conditional mass is comparable to
beta_Q. This conditional menu property is not a property of general
original global minima.

For completeness, the original independent conditional hazards satisfy

    sum_(i,n) -log(1-q_i(n))=-log nu.

For t<A/2, (30) and the completion bound give
nu>=(A/(28M))^4, and hence this total log hazard is at most
4 log(28M/A), uniformly in all finite menus and offsets. This bound by
itself neither produces absorption nor consumes diffuse hazard limits.

## 10. Generic counterexample access and native minimum selection

The theorem is not conditional on an arbitrary unproduced calendar.
A hypothetical counterexample to the signed four-player quitting-game
uniform-equilibrium conjecture supplies a table in its domain, after
normalization and generic perturbation. The normalization step uses the
tracked declarations listed in Section 12; no new formalization is claimed.

The single-pivot normalization produces a bounded table r with own
singleton one at a pivot p, all other own singletons zero, and a positive
unrestricted actual SUM-debt infimum. In particular its absorbing
infimum is positive. Subtract one from EVERY nonempty entry of recipient
p's row, leaving all other rows unchanged. Call the result Z. All its own
singletons are zero.

At any absorbing prescribed profile, its pivot prescribed payoff falls
by exactly one. Each pivot finite-response payoff also falls by one,
since a forced finite response guarantees absorption. In both tables
the supremum of finite-response payoffs includes Never: a deadline
tending to infinity converges to Never payoff plus the nonnegative own
singleton times the opponent-Never product. Thus the pivot full cap also
falls by one. Other recipients' values and caps do not change. All debts
are preserved on absorbing profiles, so the native absorbing infimum
A(Z) is positive. This does not assert affine invariance of debt on a
profile with positive joint Never mass.

Perturbing every native entry by at most delta changes each prescribed
value and each full cap by at most delta, hence every profile's SUM debt
by at most 8delta. Taking infima over the same absorbing class proves
|A(Z')-A(Z)|<=8delta. Thus sufficiently small perturbations within the
own-zero affine slice retain A>0.

Every row-equality condition is a nonzero linear polynomial on that
slice: each row's sole fixed entry is its own singleton zero, while its
other fourteen entries are independent coordinates. Each forbidden pair
condition in (1) is also a nonzero polynomial: its two singleton and two
pair entries are independent coordinates from two rows. A nonzero real
polynomial has zero set with empty interior, so the complement of this
finite union is dense and open. Choose Z' arbitrarily close with all
guards and A(Z')>0. The result applies to this perturbed positive-A
native table. This changes the table and is an existence reduction; it
does not transfer a selected old minimum to new rewards or claim a
non-generic closure theorem.

For the resulting fixed table, H_Z is compact and contains AllNever.
Let E_Z be its zero-debt subset and alpha=min_(E_Z) nu. The completion
inequality passes to H_Z and implies alpha>0. Original raised minima
exist by compactness. If X_t is any such minimum, its comparison with
an alpha-minimizing native point gives

    nu_t<=alpha,
    sum_i theta_i d_i^Z(X_t)/t<=Theta(alpha-nu_t).

Taking t->0, every limit point belongs to E_Z, so nu_t->alpha and native
weighted debt is o(t). If alpha=1, beta_t->0. If alpha<1, beta_t stays
bounded below by 1-alpha. These statements use the original raised
full-debt objective. Equations (25) and (29) therefore exclude a genuine
normalized two-owner stratum of these sources and their native tails.
They leave the beta=O(t) arm and the three/four-owner absorbing consumer
unresolved; the four-player conjecture remains open.

The improvement over a macroscopic third-tail modulus is quantitative
in the relevant small-mass normalization. A modulus assuming a fixed
positive lower bound on the largest tail does not control ratios as all
tails vanish. Likewise, total-debt censoring alone, combined with a
quadratic two-owner debt floor, gives only a third-mass bound of order
beta^2. The response-level normalization (13) instead yields a uniform
third fraction when D=o(beta^2), and (29) at EVERY nonempty exact native
whole tail, including microscopic tails. Combining this fraction with a
shared-atom lower bound would still allow large pair-only cohorts that
rotate among three or four owners. No common triple atom, common calendar,
or absorbing consumer is supplied by the dispersion theorem.

## 11. Exact boundary control and finite checks

Positive A cannot be dropped even when all generic guards hold. Encode
nonempty coalitions by bit masks m=1,...,15, with player i's bit 2^i.
Define default entries by

    Z_i(m)=10m+i+1                         for i=0,1;
    Z_i(m)=10m+i+1                         for i=2,3 and i not in m;
    Z_i(m)=-(10m+i+1)                      for i=2,3 and i in m.

Replace every own singleton by zero and make four further replacements:

    Z_0({1})=1, Z_0({0,1})=2,
    Z_1({0})=1, Z_1({0,1})=3.

Each row has fifteen distinct entries. The six determinants (1), ordered
by pairs 01,02,03,12,13,23, are exactly

    1, -2836, -8888, -4072, -10976, -4880.

Owners 0 and 1 can use defective geometric clocks with arbitrary total
finite masses f,g in (0,1). Their CONDITIONAL finite laws have hazards
z_0=1/3,z_1=1/2, namely masses f z_0(1-z_0)^n and g z_1(1-z_1)^n at
date n; the remaining masses are Never. The other owners use Never.
The active equality z_1 J_01=Gamma_01 and its reverse imply
that every active finite response equals Never, namely g for owner 0
and f for owner 1. For an outsider, Never pointwise dominates any finite
response: it earns a positive passive payoff when opponents quit;
joining them gives a negative participant payoff; preempting them gives
own singleton zero, and all-opponents-Never gives zero either way.
Thus D=0, beta=f+g>0, epsilon=0, contradicting any positive constant in
(2) without A>0. The sure geometric clock of owner 0 alone is absorbing
exact Nash by the same active equality and outsider domination, so
A=0 for this example, as required. Exact summation gives

    U=B=(g,f,13f+23g-13fg,14f+24g-14fg),
    nu=(1-f)(1-g).

At f=g=1/2 this is (1/2,1/2,59/4,31/2), with nu=1/4 and beta=1.
The sure solo profile has U=B=(0,1,13,14).

The complete reproducible programs follow. Save the first Python block as
`transfer_check.py` and the second as `dispersion_boundary_check.py` in any
scratch directory, then run with ordinary Python 3:

    python transfer_check.py
    python dispersion_boundary_check.py

Only the Python standard library is needed. The first reconstructs signed
full-table finite-law payoffs and caps in exact rational arithmetic,
including the last finite query and literal Never. Eighteen cases check
Fubini, (13), uniform query-gap transfer, and every outsider expansion (19).
The second checks the complete boundary table, row guards, pair
determinants, and geometric contact identities. These finite checks
supplement the proofs; they do not establish compactness, positive A for
any example, or the universal claim.

### 11.1. Complete finite-law transfer checker

```python
"""Exact finite-law audit of the third-owner dispersion proof's transfer steps.

This is independent finite evidence for algebraic identities and uniform query
bounds. It does not establish compactness, the absorbing-gap hypothesis, or the
dispersion theorem. Run with ordinary Python 3; only the standard library is used.
"""

from fractions import Fraction as F
from itertools import product
from random import Random


NEVER = 4
TESTS = range(5)  # 3 is a finite test after every supported finite date.
OWNERS = range(4)
RNG = Random(610417)


def payoff(z, i, dates):
    first = min(dates)
    if first == NEVER:
        return F(0)
    mask = sum(1 << j for j in OWNERS if dates[j] == first)
    return z[i][mask]


def query(z, p, i, test):
    other = [j for j in OWNERS if j != i]
    out = F(0)
    for times in product((0, 1, 2, NEVER), repeat=3):
        dates = [test] * 4
        weight = F(1)
        for j, a in zip(other, times):
            dates[j] = a
            weight *= p[j][a]
        out += weight * payoff(z, i, dates)
    return out


def responses(z, p, i):
    return [query(z, p, i, a) for a in TESTS]


def summary(z, p):
    values = [responses(z, p, i) for i in OWNERS]
    caps = [max(v) for v in values]
    pays = [sum(p[i][a] * values[i][a] for a in TESTS) for i in OWNERS]
    debts = [caps[i] - pays[i] for i in OWNERS]
    return values, caps, pays, debts


def never_law():
    return [F(0), F(0), F(0), F(0), F(1)]


def finite_law():
    weights = [RNG.randrange(1, 8) for _ in range(3)]
    total = sum(weights)
    return [F(w, total) for w in weights] + [F(0), F(0)]


def mix(finite, mass):
    return [mass * a for a in finite[:-1]] + [1 - mass]


def test_case(z, masses):
    conditional = [finite_law() for _ in OWNERS]
    p = [mix(conditional[i], masses[i]) for i in OWNERS]
    vals, caps, pays, debts = summary(z, p)
    bound = max(abs(a) for row in z for a in row)
    pruned = [p[0], p[1], never_law(), never_law()]
    qvals, qcaps, qpays, qdebts = summary(z, pruned)
    eps = masses[2] + masses[3]

    for i in OWNERS:
        w = vals[i][NEVER]
        b = caps[i] - w
        f = masses[i]
        mean_finite = sum(conditional[i][a] * vals[i][a] for a in TESTS)
        assert 0 <= b <= debts[i] / (1 - f)
        assert -b <= w - mean_finite <= debts[i] / f
        assert debts[i] == b + f * (w - mean_finite)
        for a in TESTS:
            old_gap = w - vals[i][a]
            new_gap = qvals[i][NEVER] - qvals[i][a]
            assert abs(new_gap - old_gap) <= 4 * bound * eps
            assert old_gap >= -debts[i] / (1 - f)

    for i, j in ((0, 1), (1, 0)):
        sure = [never_law() for _ in OWNERS]
        sure[j] = conditional[j]
        vv = responses(z, sure, i)
        bb = max(vv)
        pp = sum(conditional[i][a] * vv[a] for a in TESTS)
        gamma = z[i][1 << j]
        fi, fj = masses[i], masses[j]
        assert vv[NEVER] == gamma
        assert qcaps[i] == fj * bb
        assert qpays[i] == fj * ((1 - fi) * gamma + fi * pp)
        assert qdebts[i] == fj * (1 - fi) * (bb - gamma) + fi * fj * (bb - pp)
        for a in TESTS:
            assert qvals[i][NEVER] - qvals[i][a] == fj * (gamma - vv[a])
        assert 0 <= bb - gamma <= debts[i] / ((1 - fi) * fj) + 4 * bound * eps / fj
        assert 0 <= bb - pp <= debts[i] / (fi * fj) + 4 * bound * eps / fj
        assert -debts[i] / ((1 - fi) * fj) - 4 * bound * eps / fj <= gamma - pp
        assert gamma - pp <= debts[i] / (fi * fj) + 4 * bound * eps / fj

    pair = [conditional[0], conditional[1], never_law(), never_law()]
    for h in (2, 3):
        solo = []
        for j in (0, 1):
            law = [never_law() for _ in OWNERS]
            law[j] = conditional[j]
            solo.append(responses(z, law, h))
        both = responses(z, pair, h)
        g0, g1 = z[h][1], z[h][2]
        for a in TESTS:
            remainder = both[NEVER] - g0 - g1 - both[a] + solo[0][a] + solo[1][a]
            assert abs(remainder) <= 6 * bound
            expression = masses[0] * (g0 - solo[0][a]) + masses[1] * (g1 - solo[1][a])
            expression += masses[0] * masses[1] * remainder
            assert qvals[h][NEVER] - qvals[h][a] == expression


def main():
    cases = 0
    for _ in range(3):
        z = [[F(RNG.randrange(-7, 8)) for _ in range(16)] for _ in OWNERS]
        for i in OWNERS:
            z[i][0] = z[i][1 << i] = F(0)
        for scale in (1, 10, 100):
            for masses in (
                (F(2, 3 * scale), F(1, 2 * scale), F(1, 13 * scale**2), F(1, 17 * scale**2)),
                (F(1, 2 * scale), F(1, 19 * scale), F(1, 23 * scale**2), F(1, 29 * scale**2)),
            ):
                test_case(z, masses)
                cases += 1
    print(f"PASS: {cases} exact signed full-table/profile cases")
    print("PASS: Fubini branch bounds and pure-query/Never pruning bounds")
    print("PASS: normalized active-pair debt, cap, and contact transfer identities")
    print("PASS: every outside query's pair/solo expansion and remainder bound")


if __name__ == "__main__":
    main()
```

### 11.2. Complete boundary-table checker

```python
"""Exact arithmetic for the zero-absorbing-gap dispersion boundary control.

Run with:
    python dispersion_boundary_check.py

The complete table has own singleton zero, distinct entries in each row,
and six nonzero passive/joining cross determinants.  Owners 0 and 1 use
finite masses f,g in (0,1), with conditional finite laws z_i*rho_i**n;
their remaining masses are literal Never.  Owners 2 and 3 use Never.

This checks the exact coefficients proving all-date active indifference,
geometric first-coalition weights, and the outsider inequalities that
hold pointwise for every realization of the opponents' clocks.  Those
identities price arbitrary complete behavioral deviations by averaging
pure finite/Never responses.  This is not an infinite-profile brute-force
test and is not a Lean proof.  The explicit absorbing solo construction
has zero full debt, so the positive absorbing-gap hypothesis fails.
"""

from fractions import Fraction as F
from itertools import combinations


OWNERS = range(4)
MASKS = range(1, 16)


def make_table():
    table = {}
    for owner in OWNERS:
        for mask in MASKS:
            value = F(10 * mask + owner + 1)
            if owner >= 2 and mask & (1 << owner):
                value = -value
            if mask == 1 << owner:
                value = F(0)
            table[owner, mask] = value
    table[0, 2] = F(1)
    table[0, 3] = F(2)
    table[1, 1] = F(1)
    table[1, 3] = F(3)
    return table


def main():
    table = make_table()
    assert len(table) == 60
    for owner in OWNERS:
        assert table[owner, 1 << owner] == 0
        assert len({table[owner, mask] for mask in MASKS}) == 15

    gamma = {
        (i, j): F(0) if i == j else table[i, 1 << j]
        for i in OWNERS for j in OWNERS
    }
    joining = {
        (i, j): F(0) if i == j else table[i, (1 << i) | (1 << j)]
        for i in OWNERS for j in OWNERS
    }
    determinants = {}
    for i, j in combinations(OWNERS, 2):
        determinant = (
            gamma[i, j] * joining[j, i]
            - gamma[j, i] * joining[i, j]
        )
        assert determinant != 0
        determinants[i, j] = determinant

    z = {0: F(1, 3), 1: F(1, 2)}
    rho = {i: 1 - z[i] for i in (0, 1)}
    for i in (0, 1):
        assert 0 < z[i] < 1
        assert 0 < rho[i] < 1
        assert z[i] / (1 - rho[i]) == 1

    # Against opponent j with finite mass F_j, a pure date-n response is
    # F_j * [Gamma_ij + rho_j**n * (z_j*J_ij - Gamma_ij)].
    # The zero second coefficient proves equality with Never for EVERY n.
    for i, j in ((0, 1), (1, 0)):
        assert z[j] * joining[i, j] - gamma[i, j] == 0

    # Conditional on BOTH owners being finite, these geometric sums are
    # respectively the probabilities of 0 first, 1 first, and a tie.
    denominator = 1 - rho[0] * rho[1]
    first_zero = z[0] * rho[1] / denominator
    first_one = z[1] * rho[0] / denominator
    tie = z[0] * z[1] / denominator
    assert (first_zero, first_one, tie) == (F(1, 4), F(1, 2), F(1, 4))
    assert first_zero + first_one + tie == 1

    # Polynomial coefficients in the basis (f, g, f*g).  For arbitrary
    # real f,g in (0,1), the first-coalition probabilities are these
    # polynomials, and the remaining probability is (1-f)*(1-g).
    weights = {
        1: (F(1), F(0), first_zero - 1),
        2: (F(0), F(1), first_one - 1),
        3: (F(0), F(0), tie),
    }
    assert tuple(sum(weights[mask][k] for mask in (1, 2, 3))
                 for k in range(3)) == (F(1), F(1), F(-1))
    prescribed = {
        i: tuple(sum(table[i, mask] * weights[mask][k] for mask in (1, 2, 3))
                 for k in range(3))
        for i in OWNERS
    }
    assert prescribed[0] == (F(0), F(1), F(0))
    assert prescribed[1] == (F(1), F(0), F(0))
    assert prescribed[2] == (F(13), F(23), F(-13))
    assert prescribed[3] == (F(14), F(24), F(-14))

    # For an outsider, compare Never with a fixed finite deadline for
    # each realization of the opponents' clocks.  If opponents quit
    # earlier, both responses receive the same payoff.  If they quit
    # exactly at the deadline, joining receives <=0 instead of >0.
    # If they quit later, quitting now receives own-singleton 0 instead
    # of >0; if they all Never, both responses receive 0.
    for outsider in (2, 3):
        own_bit = 1 << outsider
        for mask in MASKS:
            if not mask & own_bit:
                assert table[outsider, mask] > 0
                assert table[outsider, mask | own_bit] < 0
                assert table[outsider, mask] >= table[outsider, own_bit]
            elif mask != own_bit:
                assert table[outsider, mask] < 0

    # These same pointwise inequalities apply when owner 0 alone uses a
    # sure geometric law.  Its payoff/cap is 0.  Owner 1's EVERY finite
    # response equals Never=Gamma_10 by the already checked contact.
    # Outsiders' Never responses dominate pointwise.  Thus this actual
    # absorbing profile has U=B=(0,1,13,14), proving A_abs=0.
    assert z[0] / (1 - rho[0]) == 1
    assert z[0] * joining[1, 0] == gamma[1, 0]
    solo_payoffs = tuple(table[i, 1] for i in OWNERS)
    assert solo_payoffs == (F(0), F(1), F(13), F(14))

    # A rational defective instance makes the failed dispersion conclusion
    # explicit: D=0, beta=1, and the two smallest finite masses are zero.
    f = g = F(1, 2)
    basis = (f, g, f * g)
    instance_payoffs = tuple(
        sum(prescribed[i][k] * basis[k] for k in range(3))
        for i in OWNERS
    )
    assert instance_payoffs == (F(1, 2), F(1, 2), F(59, 4), F(31, 2))
    assert (1 - f) * (1 - g) == F(1, 4)
    assert f + g == 1

    guard_text = ", ".join(
        f"{i}{j}:{value}" for (i, j), value in determinants.items()
    )
    print("PASS: all 60 rewards, own-zero, and distinct entries in every row")
    print(f"PASS: six nonzero cross determinants ({guard_text})")
    print("PASS: exact all-date active contacts and arbitrary-f,g payoff identities")
    print("PASS: outsiders' pointwise Never dominance prices every behavioral response")
    print("PASS: absorbing solo geometric Nash proves A_abs=0")
    print("PASS: defective example has D=0, beta=1, epsilon=0, and nu=1/4")


if __name__ == "__main__":
    main()
```

## 12. Tracked semantic declarations and scope

The complete-law/full-cap interpretation is given by
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
`quittingTerminalSemanticCarrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` is the original
closure of prescribed values and full behavioral response caps.

The counterexample source uses
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` and
`exists_finFour_no_uniformPayoff_iff_exists_singlePivot` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.
The source includes positive pivot, canonical own rewards, preserved
absence of a uniform payoff, and a strictly positive actual profile floor.
The terminal semantic endpoint is
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`.
The precise delayed finite-response identity used in the absorbing row
shift is `quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.

These declarations were inspected under their stated imports; no Lean
or Lake command was run for this manuscript. The dispersion theorem,
its constants, and its consumers above are ordinary mathematics.

## 13. Mathematical contracts for a later formalization

The primary target has the following ordinary mathematical shape:

    fixed bounded own-zero Fin4 table Z,
    A(Z)>0, row distinctness, and the six pair guards
      -> exists c>0, forall actual independent complete profiles P,
           D_Z(P)+beta(P) epsilon(P)>=c beta(P)^2.

Here D_Z is the SUM of the four unrestricted behavioral response debts,
beta is the sum of the four original finite masses, and epsilon is the
sum of the two smallest such masses. The sorting operation can equivalently
be replaced by the minimum, over all pairs of kept owners, of the remaining
finite mass. The constant may depend on Z; no computable modulus is asserted.
This is a theorem about all actual profiles, with no source-selector premise.

The augmented-closure version follows by continuity of (U,B,N), with
original Never coordinates retained. The quantitative moving-cut target
is exactly (28), for each supplied actual whole cut and original collar
kappa>0. It requires no conditional minimum assumption. A retained-cut
version must include actual matching whole-cut realizers as constructed
in Sections 5 and 8; arbitrary abstract-clock execution is not a premise
one may silently drop.

The original-minimum consumer combines that theorem with the exact raise
identities and actual AllNever comparison to obtain (25). The finite-menu
consumer instead uses (30)--(31); the two source hypotheses remain distinct.
The zero-debt conditional-tail consumer uses (29) and no minimum-Never
selection. For approximate moving cuts the implementation must retain the
term D(P)/(2 kappa^3 R) rather than erase it when R tends to zero.

The compact-clock proof, same-chart unary kernel convergence, geometric
support exhaustion, and actual absorbing solo construction are all required
mathematical obligations in such a formalization. The finite programs are
checks of algebraic instances and boundary identities, not substitutes for
these arguments. The surviving task is an absorbing low-debt producer
for the remaining three/four-owner configurations, including the raised
beta=O(t) branch; no further conditional producer interface is claimed here.
