# Ordered finite activity and a required third-player tail

## Statement

Four players independently choose complete first-Quit laws on natural dates and a separate literal Never. Before absorption there is one live public history at each date. A law is implemented by its conditional hazards. Every unilateral behavioral strategy likewise determines one complete law, and a player may replace its whole law using private randomization. At the first nonempty coalition S of quitters player l receives the finite reward Z_l(S). Live, all-Never and own-singleton rewards are zero. Fix M>=1 bounding all absolute rewards.

For an actual profile let U_l be its expected terminal payoff and B_l its complete unilateral response supremum. All mixed responses average the pure finite deadlines and Never. Put d_l=B_l-U_l, D=sum_l d_l, and let A be the infimum of D over actual profiles absorbing almost surely. Assume A>0 at this fixed table. Write N_l for the original marginal Never probability. At any old finite query x put

    R_l(x)=Pr(x<=T_l<Never), beta(x)=sum_l R_l(x),
    H_ij(x)=Pr(x<=T_i<=T_j<Never).

These are unconditional physical clock probabilities. Dates tied between i and j are included. Draws remain independent even when another player stops earlier. Let i,j,u,v be the four distinct players. For every nonempty S contained in {u,v} assume

    Z_i(S)>=max(0,Z_i(S union {i})),
    m=min_(l=u,v) min(Z_i({l}), Z_i({l})-Z_i({i,l}))>0.       (G)

**Ordered activity theorem.** There exists an explicit c>0, depending only on the fixed table and A, such that every actual profile at EVERY x satisfies

    D+H_ij(x)>=c R_i(x)^2.                                   (O)

At zero debt this forces R_j(x)>=c R_i(x) whenever R_i(x)>0. It also excludes finite stopping mass of i which stays large while the probability of j stopping at or after i tends to zero. At a macroscopic positive-debt source this latter conclusion applies whenever its original D tends to zero at the same fixed table.

**Named owner theorem.** Put Gamma_ab=Z_a({b}) and J_ab=Z_a({a,b}) for a!=b. Assume additionally that the remaining pair {u,v} has one orientation (u,v) with

    Gamma_uv(Gamma_uv-J_uv)>0,    Gamma_vu!=0.               (P)

There exists c'>0 at the fixed table such that every actual profile, at every original finite cut, obeys

    D+beta(x) R_j(x)>=c' beta(x)^2.                          (N)

Thus every nonempty zero-debt finite tail places at least the fraction c' of its total mass on the specified player j. This includes four positive cofinal streams whose normalized masses might otherwise approach a three-player face. For i=2,j=3,u=0,v=1, conditions (G),(P) follow already from the following literal rewards and comparisons:

    Z2(0)=1, Z2(1)=3, Z2(01)=4,
    Z2(02),Z2(12),Z2(012)<=0,
    Gamma01=-2, J01=-1, Gamma10=-6.

The remaining entries may vary arbitrarily, subject to the native normalization and A>0. The pair01 test does not use J10. No row-distinctness, joining-ratio genericity, full singleton-matrix rank, minimum selection, atomic support or bound on durations is required.

## A bound at each original query

Fix any player h and original finite query y. Write C_h=product_(l!=h)N_l. If R_h(y)>0 put z=Pr(T_h=y)/R_h(y). Consider a responding player k!=h. Against the original opponents, compare the pure y response with literal Never. Any opponent exit strictly before y cancels. When both opponents outside {k,h} choose Never, the difference, deadline minus Never, equals

    (product_(l outside {k,h})N_l) R_h(y) [z J_kh-Gamma_kh].

Indeed an h exit at y changes passive Gamma_kh to joint J_kh, a later finite h exit changes it to zero, and the all-Never branch gives zero under both responses. Every remaining outcome with nonzero difference involves a finite exit at/after y by at least one opponent outside {k,h}. Thus the error in this formula has absolute value at most 2M sum_(l outside {k,h})R_l(y).

Let e_k be the value of the original Never response. The nonnegative full-cap excess B_k-e_k is at least the positive part of the deadline-minus-Never difference. Full-law Fubini gives d_k>=N_k(B_k-e_k). Multiply the preceding estimate by N_k, use N_k<=1 on the error, and sum over k!=h. Each other finite tail occurs in exactly two error sums. This gives

    D>=C_h R_h(y) sum_(k!=h)(z J_kh-Gamma_kh)^+
                            -4M sum_(l!=h)R_l(y).

For z in (0,1], let h use an actual sure finite geometric law with hazard z, with every other player Never. Against this law k earns Gamma_kh from Never and Gamma_kh+(1-z)^n(z J_kh-Gamma_kh) from a pure date n. At z=1 date zero pays J_kh and later dates pay Gamma_kh. Player h has value and cap zero. Hence the actual absorbing profile's total debt equals sum_(k!=h)(z J_kh-Gamma_kh)^+. This bounds A from above. At z=0 let positive z decrease to zero in this continuous numeric formula. We obtain

    D>=C_h A R_h(y)-4M sum_(l!=h)R_l(y).                     (C)

When R_h(y)=0 this bound follows from D>=0.

If D<A/2, move the smallest marginal Never mass to one finite date. An owner becomes surely finite, so the resulting actual profile absorbs. Under the natural coupling, each of the four prescribed payoffs and each of the three other owners' full caps changes by at most 2M times the moved mass. The moving player's own cap is unchanged. Thus A<=D+14M min_l N_l. In particular every original N_l is at least eta=A/(28M)>0 in this low-debt branch. We may use this stronger individual collar directly. A<=8M by the reward bound, so eta<1.

## Integrating the specified owner's response

Let v_i(y) denote the value to i of the pure finite deadline y. On the event j chooses Never and no opponent stopped before y, the first finite opponent coalition, if any, is contained in {u,v}. Its passive reward is nonnegative by (G). If that coalition stops at y, the difference e_i-v_i(y) on that outcome is the passive reward less the joint participation reward. If the coalition stops strictly later, that difference is the passive reward less zero. These comparisons are nonnegative. Keeping just the events in which exactly one of u,v has a finite draw at/after y and the other is Never gives, by independence,

    e_i-v_i(y)>=m N_j[N_v R_u(y)+N_u R_v(y)]-2M R_j(y).      (1)

A j exit strictly before y cancels, so every possible negative contribution belongs to the displayed error event. This calculation retains the full reward at all ties.

Use the original i-law restricted to [x,Never), excluding its Never atom, to integrate (1) in y. On that restricted domain, the integral of e_i-v_i(y) is at most the integral of the nonnegative losses B_i-v_i(y), hence at most the full d_i. Consequently

    m eta^2 [H_iu(x)+H_iv(x)]<=D+2M H_ij(x).                 (2)

Next integrate (C), for h=i, against the SAME restricted law. For independent copies of i, exchange their labels to obtain

    integral_[x,Never) R_i(y) dq_i(y)
      =[R_i(x)^2+sum_(finite y>=x) q_i({y})^2]/2.

This includes a nonatomic finite part if the clock has one. With R_i(x)<=1 and (2), integration gives

    eta^3 A R_i(x)^2/2
       <=D+4M[H_iu(x)+H_iv(x)+H_ij(x)]
       <=[1+4M/(m eta^2)]D+4M[1+2M/(m eta^2)]H_ij(x).

Take L=max(1+4M/(m eta^2),4M[1+2M/(m eta^2)]) and c=min(A/2,eta^3 A/(2L)). This proves (O) at low debt. If D>=A/2, the D term alone gives (O), since R_i(x)<=1. The implication for the two marginal tails follows from independence and H_ij(x)<=R_i(x)R_j(x).

## The remaining pair and all old cuts

We first prove a uniform version of (N) for total finite masses f_l at the start, beta=sum f_l, on any of the ordered profiles under consideration with every N_l>=eta. Suppose there were a sequence at the same fixed table with beta>0 and

    D/beta^2 ->0,     f_j/beta ->0.

Equations (1),(2),(C) and their integral used only the original positive collar. They therefore give (O) on this sequence at its first query. Since H_ij<=f_i f_j<=beta f_j, one obtains f_i/beta->0. Relabel the larger mass among u,v as h along a subsequence, and denote the other by g. The normalized h mass has lower limit at least 1/2. At the INITIAL original legal query every R_l=f_l. Equation (C) shows

    eta^3 A f_h<=D+4M(f_g+f_i+f_j).

It follows that both f_u and f_v are bounded below by a fixed positive multiple of beta. In particular their normalized finite laws F_u,F_v are defined on the same original clock.

For l=u,v write p_l for its response using F_l against its original opponents. Complete-law Fubini gives d_l=N_l(B_l-e_l)+f_l(B_l-p_l). Both differences are nonnegative. Hence |e_l-p_l|<=D/N_l+D/f_l. Replace the finite draws of i and j by their own Never branches, keeping the normalized responding law unchanged. A coupling changes each of the two tested responses by at most 2M(f_i+f_j). After this censoring, the opponent-Never branch gives zero under both responses. The difference of responses against a sure finite opposite law, denoted L_l, now satisfies (with w the other of u,v)

    |L_l|<=[D/N_l+D/f_l+4M(f_i+f_j)]/f_w ->0.

The last limit uses beta<=4, the two lower bounds on masses and the original Never collar. Against independent X~F_u,Y~F_v put a=Pr(X<Y), b=Pr(Y<X), z=Pr(X=Y), so a+b+z=1. Exactly,

    L_u=Gamma_uv a+(Gamma_uv-J_uv)z,
    L_v=Gamma_vu b+(Gamma_vu-J_vu)z.

The two coefficients in L_u have the same strict sign by (P). Thus a,z tend to zero and b tends to one. The limit of L_v is Gamma_vu!=0, a contradiction. We have proved the existence of d>0 at this fixed table and fixed eta with

    D+beta f_j>=d beta^2

for all such profiles. This argument gives the same d across different ordered clocks: it used only the common fixed table, positive collar, independent laws, full response tests and (C).

Return to an original old cut x. If D>=A/2, the bound (N) follows with c'<=A/32 since beta(x)<=4. Otherwise N_l>=eta. Condition each law on survival to x, whose probability n_l=N_l+R_l(x)>=eta. The conditional original Never is at least eta, and its finite mass is f_l^x=R_l(x)/n_l. Let D_x be total full debt of these independent conditional laws, with the entire current query retained. To implement any conditional deviation, keep the old own law strictly before x and replace its conditional surviving law by this deviation. The gain over the original play is exactly product_l n_l times the conditional gain. Earlier absorption events cancel. Thus D>=eta^4 D_x. No new query is inserted before the retained cut. Apply the total-mass bound to this conditional clock and put beta_x=sum f_l^x. We have beta(x)>=eta beta_x and R_j(x)>=eta f_j^x, while beta_x>=beta(x). Therefore

    D+beta(x)R_j(x)>=eta^4 [D_x+beta_x f_j^x]>=eta^4 d beta(x)^2.

Taking c'=min(A/32,eta^4 d) proves (N).

## Original source and scope

The proof of (1) and (C) is valid on any complete retained ordered set of old queries bearing independent laws, their literal earliest-coalition kernels, a separate original Never and the Fubini meaning of all original caps and payoffs. The set may be compact with an empty terminal mark. Its first query and every cut used in the proof must be legal. The only new strategic comparator in (C) is the actual absorbing solo law at the same table. The repair estimate extends by continuity in D,N to the Euclidean closure of actual augmented tuples (U,B,N). Thus (O),(N) hold for every such tuple equipped with its genuine retained representation, directly on its query set. The conditional proof uses the original N collar and conditional Fubini. No calendar compression, omitted tie, actual realization of the limiting law, or advance of common public randomness is needed. The order probability H belongs to the supplied retained representation. The total-mass version of (N), which only depends on D,N, extends to the tuple closure itself by continuity, even without choosing a representation.

For a nontrivial native zero-debt tail at the displayed literal data, normalized finite masses approaching the face with missing player3 are excluded even when all four owners remain physically cofinal. Further, along any fixed-table sequence of actual or genuinely represented sources with D tending to zero and f2 bounded below, (O) forces H23 bounded below. This excludes entirely reverse-ordered or asymptotically reverse-ordered macroscopic finite excursions, including when all four owners have finite activity. The only extra input to this last application is the stated lower bound on f2, which is not needed by the main theorem. The result allows a common 23 atom. It does not force strict time ordering, observed actions by a preempted player, or equilibrium existence for arbitrary four-player games. The native A is an absorbing infimum, distinct from the unrestricted terminal infimum. Native AllNever has zero debt.

## Boundary tests

Consider a recipient i facing singletons u,v paying 1,3 and pair uv paying4, with all i-participation rewards zero. Let u stop at time0 with mass 1/4, v stop at time1 with mass 1/2, and j always choose Never. Then e_i=1/4+3(3/4)(1/2)=11/8. Query0 gives0. Query1 gives1/4, from the earlier u exit, and thus the gap is 9/8. At query1 the full v contribution on the event u=Never is exactly 9/8. These values illustrate inclusion of the current v atom and cancellation of the strictly earlier exit. If additionally i=2 uses finite mass 1/3 at time1, then the total Never-minus-prescribed expectation equals (1/3)(9/8)=3/8 and bounds its own debt from below, with H_ij=0.

The assumption A>0 matters globally. Give each player reward 1 at every opposing singleton and 0 at every other coalition, except set Z_i(uv)=1 so (G) still holds. All own-singletons and AllNever pay0. Condition (P) holds. Let i stop surely at time0 and others Never. Every outsider already receives1, the largest table reward, and i receives0 from every reply. This absorbing profile has D=0=f_j=H_ij, but f_i=beta=1. All raw reward comparisons hold and A=0. This example also works with any positive i mass less than one, since a pure outsider deadline cannot improve over waiting for i. Original N may thus be positive as well.

To see why (1) keeps the joint participation comparison, change Z_i(uv) to -1 while the iuv payoff remains0. If u,v share one sure atom and j is Never, e_i=-1 while quitting together gives0. Positive singleton rewards alone cannot supply the claimed nonnegative event decomposition.

## Source correspondence and handoff

`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile` and `quittingBehaviorStoppingLaws_stoppingLawProfile` in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean` identify the operational complete-law caps and the conditional-hazard representation. `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean` identifies the uniform-payoff existence target reached by terminal approximate Nash at every error. Neither endpoint supplies A>0 for the normalized table. Here the source premise is the explicitly fixed absorbing gap. The output is a restriction on every independent profile and on complete represented zero-debt sources, including the chronology of a named owner relative to another. It does not produce uniform equilibrium.

A formalization can first define inclusive finite suffix masses and the ordered independent law probability, then prove the one-query comparisons and integrate. The solo test is a natural-clock comparator independent of the original marked calendar. Conditional-law Fubini transports the last inequality to every old cut. Neither an equilibrium of an auxiliary game nor the lower bound on a named owner should enter as a structure field. This is ordinary mathematics. No new Lean declaration or build is claimed.
