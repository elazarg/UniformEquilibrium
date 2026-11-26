# Original full debt and END caps control every finite tail

Full unilateral debt controls the finite tails at every offered clock
query. If the other three owners have END as a best response, one finite
tail cannot asymptotically dominate their combined tails at a positive
native absorbing gap. The resulting absorbing-profile consumer allows
arbitrary earlier play and any number of cofinal streams.

## 1. Exact native data, original clocks and theorem

Fix four players I and a bounded native reward Z_i(S) for every recipient
i and nonempty first quitting coalition S. All native own rewards are
zero: Z_i(i)=0. Live play and literal AllNever pay zero. Put

    M=max(1,max_(i,S)|Z_i(S)|),
    A=inf{D_Z(P): P is ACTUAL and absorbs almost surely},
    Gamma_il=Z_i(l), J_il=Z_i(il) for i!=l.          (1)

Here D is the SUM of four unrestricted unilateral debts. A deviation
replaces one complete behavioral clock; every pure finite date, literal
Never and every mixture is priced. Actual players privately draw their
complete clocks independently. J is the joint participant reward, not the
joining difference J-Gamma. There is no sign or genericity assumption.

Take actual complete laws, or a complete ORIGINAL retained representation
with its entire offered finite test set T, final empty finite END=c,
independent first-coalition kernels and separate ORIGINAL Never. Let

    N_i=P_i(Never)>0, nu=PRODUCT_i N_i>0,
    R_i(x)=P_i([x,c)), mu_i(x)=P_i({x}).            (2)

The finite tail R includes the query x and excludes Never. It includes
ROOT mass when x is ROOT. At an actual natural-calendar profile, empty
END can instead mean the limiting finite response. The native own-zero
limit equals literal Never. No retained law is presumed executable.

Fix any h and ANY offered x with R_h(x)>0. For TheoremA suppose EACH of
the three observers i!=h has END among its ENTIRE finite full-cap
maximizers. Their other cap sets can be arbitrary. TheoremB below has
NO END-cap hypothesis. Neither theorem assumes a number of finite/cofinal
streams, a tie pattern, relative support, CURRENT ROOT support, a minimum,
a special selector, or optimality of a conditional suffix. Set

    T_h(x)=SUM_(j!=h)R_j(x), z=mu_h(x)/R_h(x) in[0,1].

**Theorem A, exact quantitative consumer.**

    A <= SUM_(i!=h)(z J_ih-Gamma_ih)^+
      <= 18M T_h(x)/(nu R_h(x)).                  (3)

The first inequality is consumed by ACTUAL absorbing solo clocks. If
z>0, the displayed middle quantity is EXACTLY their unrestricted SUM
debt; if z=0 it is the limit of the debts of actual positive-hazard
solo clocks. There is no fictitious absorbing zero-hazard law.

Consequently, at native A>0,

    T_h(x)/R_h(x) >= nu A/(18M).                   (4)

**Theorem B, unrestricted every-cut debt bound.** WITHOUT any END-active
owner assumption, put C_h=PRODUCT_(i!=h)N_i. Then at EVERY offered query,

    D_Z >= C_h A R_h(x)-18M T_h(x).                (B1)

If R_h=0 the inequality is immediate. At raised original global minima
with theta in[1/2,1], D_Z<=8t and therefore

    C_h A R_h(x)<=8t+18M T_h(x).                   (B2)

With A>0 and a uniform positive Never collar, a finite tail cannot dominate
the others while also being large relative to the raise t. This is an
EVERY-CUT restriction, including
arbitrary earlier finite play; it is not only a bound on total future
masses after one ROOT.

For A>0, (4) holds at EVERY such query without a limiting argument. In
particular no source with all observer ENDs active and positive original
Never masses can have queries x_n with R_h(x_n)>0 and

    T_h(x_n)/R_h(x_n) -> 0.                        (5)

The queries need not tend to END for this implication. If they do,
the ENTIRE asymptotically dominant late-tail class is excluded, with
arbitrary three-/four-future geometry and arbitrary finite tie mass.
No eventual atom/contact/geometric-calendar producer is assumed.

If ALL FOUR owners are END-active, (4) holds for EVERY owner with positive
finite tail. Thus after any cut a counterexample source must keep the
largest tail comparable to the sum of the other three tails. This does
not imply all four tails are comparable, a periodic calendar, support
inclusion, or a reduction to two cofinal owners.

## 2. Exact coalition expansion and the paid multifinite remainder

Fix a responding observer i. Before considering any approximation,
partition the independent opponent draws as follows. If at least one
opponent quits STRICTLY before x, forcing i at x or at empty finite END
gives the same earlier passive first coalition, including all ties there.
The two response payoffs cancel on this whole event. On its complement
every opponent draw is finite at/after x or is literal Never.

If all opponents choose Never, both finite replies pay native own zero.
If exactly ONE opponent l is finite at/after x and all others are original
Never, an l draw at x gives passive Z_i(l) at END versus joint Z_i(il)
at x. A strict later draw gives passive Z_i(l) at END versus own zero
at x. Thus the exact single-finite contribution is

    b_il[Gamma_il R_l(x)-J_il mu_l(x)],
    b_il=PRODUCT_(j!=i,l)N_j.                     (6)

All remaining nonzero events have at least TWO opponents finite at/after
x. Their first coalitions can be any pairs, triples or the responding
grand coalition. The difference between the two forced payoffs is at most
2M in absolute value. Independence and the union bound give the EXACT
expansion with a simultaneous remainder bound

    Delta_i(x):=V_i(END)-V_i(x)
      =SUM_(l!=i)b_il[Gamma_il R_l-J_il mu_l]+E_i(x),
    |E_i(x)|<=2M SUM_(l<k; l,k!=i)R_l R_k.         (7)

The bound does not discard simultaneous quitting or replace a triple by
a singleton payoff. Original early ROOT exits and all finite heads have
already canceled on their actual events. Both sums and the remainder
refer to the same ORIGINAL independent laws. This is also a pointwise
identity of any complete retained old first-coalition kernels.

Now i!=h. Write u,v for the other two opponents different from h,i, and
T=T_h(x). Since all tails are probabilities in[0,1],

    R_h(R_u+R_v)+R_u R_v <= 2T.

Hence |E_i|<=4M T. Each non-h single-finite summand in(7) has absolute
value at most2M R_l, since b_il<=1, |Gamma|,|J|<=M and mu_l<=R_l.
Their sum is at most2M T. Therefore

    Delta_i(x)
      =b_ih R_h(x)[Gamma_ih-z J_ih]+e_i(x),
    |e_i(x)|<=6M T, b_ih>=nu>0.                  (8)

The last lower bound follows from nu=N_i N_h b_ih and N_i N_h<=1.
No division by an untracked conditional survival has occurred.

By END activity Delta_i(x)>=0. Rearranging(8) and dividing by the
positive b_ih R_h gives

    (z J_ih-Gamma_ih)^+
        <=6M T/(nu R_h), i!=h.                   (9)

Summing the three bounds proves the SECOND inequality in(3). The
constants6 and18 are convenient uniform bounds, not a sharpness claim.
No error term is hidden behind the words "sufficiently late."

## 3. Actual absorbing producer, including the scalar endpoint

For EVERY 0<z<1, use the NEW actual natural-clock profile where h is
surely finite with mass z(1-z)^m on each m=0,1,..., and the other three
players choose Never. Its prescribed native payoff is the SAME vector

    v_h=0, v_i=Gamma_ih for i!=h.                 (10)

The profile absorbs almost surely. A forced finite observer deadline m
has exact value

    Gamma_ih+(1-z)^m[z J_ih-Gamma_ih].             (11)

Literal Never earns Gamma_ih. Affinity in the observer's complete clock
therefore gives its full cap Gamma_ih+(z J_ih-Gamma_ih)^+. Owner h has
payoff and full cap zero against all-Never opponents. Consequently

    D_Z(Solo_h^z)=SUM_(i!=h)(z J_ih-Gamma_ih)^+.

This proves the FIRST inequality in(3) for z in(0,1). At z=1, h surely
quits date zero; the observer's choices are joint J_ih at zero or passive
Gamma_ih at any later date/Never, giving the same formula separately.

At z=0, only take the limit of this finite REAL-valued debt formula as
actual positive hazards e decrease to zero. The debt is continuous in
e, while every profile with e>0 still absorbs and has payoff(10).
Thus A<=SUM(-Gamma_ih)^+ at this scalar endpoint as well. This completes
TheoremA without treating a nonabsorbing zero-hazard clock as actual.

When the right side of(3) is zero, z>0 gives an ACTUAL absorbing exact
Nash equilibrium. At z=0 all Gamma_ih>=0, and positive hazards e give
debt at most e SUM max(J_ih,0), hence actual absorbing approximate Nash
at every error. The native SOLO reward vector(10) stays fixed throughout.

## 4. The unrestricted every-cut debt inequality

The native full cap contains Never, and native empty END equals Never.
For each observer define its NONNEGATIVE cap excess

    kappa_i=B_i-V_i(Never)>=0.

Fubini and the complete prescribed law give the exact decomposition of
debt into the expected pure-response deficits. Its original Never branch
has mass N_i, and every other deficit is nonnegative. Hence

    d_i>=N_i kappa_i.                             (U1)

This step uses ORIGINAL Never, not a later event relabeled as Never.
From(8) and the pure-query cap inequality,

    kappa_i >= [V_i(x)-V_i(Never)]^+
             >= b_ih R_h (z J_ih-Gamma_ih)^+-6M T. (U2)

The elementary bound (a+e)^+>=a^+-|e| justifies the second inequality
with either sign of the native coefficient. Multiplying by N_i makes
the SAME leading factor for ALL three observers:

    N_i b_ih=PRODUCT_(j!=h)N_j=C_h.

Sum(U1)--(U2), use SUM_(i!=h)N_i<=3 and d_h>=0, and apply Section3's
actual absorbing solo ledger. This yields

    D_Z >= C_h R_h SUM_(i!=h)(z J_ih-Gamma_ih)^+-18M T
        >= C_h A R_h-18M T.

This proves(B1) with no cap-mode premise and for ALL offered cuts. In
particular when the other three finite laws end before x, T=0 and
D_Z>=C_h A R_h. The proof never normalizes an abstract retained suffix
and calls it executable: its only new strategic objects are the actual
natural-clock solo profiles already evaluated in Section3.

## 5. Complete original source and all-query representation

For a CURRENT fixed bounded table r, let H_r be the closure of ACTUAL
tuples(U,B,N), where N contains the four literal Never probabilities.
Its projection onto(U,B) is exactly the original semantic carrier:
lift an actual realizing sequence and extract its bounded N vector for
one inclusion; project any augmented limit for the reverse. Boundedness
and closedness make H_r compact and nonempty. A global minimum of D
therefore exists, with the same infimum as the literal actual profiles.

Here is a complete retained-clock representation of EVERY such augmented
point; it supplies the original data used in(2). Choose an actual realizing
sequence. At index m truncate a sufficiently far finite tail and move
only its vanishing total mass e_m to the SAME owners' Never branches.
Independent coupling changes every prescribed and pure-response payoff
by at most2L e_m, with L bounding current rewards. The bound is uniform
over EVERY finite/Never replacement, hence also over full caps. Thus
finite-support realizers can be used with the SAME limiting(U,B,N).
No nonvanishing escaping finite mass is redefined to be Never.

At each finite realizer use the mean clock law of the four owners.
Each occupied old date receives a chronological raw interval in[0,1]
of length its mean mass; Never receives the last interval. Owner i's
density on a whole old interval is its mass divided by the mean mass,
hence is in[0,4]. Raw coordinates are sampled INDEPENDENTLY; this
deterministic chart is not a public lottery. Extract weak-star limits
of the bounded densities and the finite/Never boundary c_m->c_*.
The bounded weak-star ball has separable L1 predual, so sequential
extraction suffices.

Keep TWO distinct compact sets of raw positions. E_m contains every
old interval endpoint and0,c_m,1. T_m contains the actual offered pure
query: midpoint for an occupied old date, its raw cut for an EMPTY
old date, and the final empty finite test c_m. In particular an unoffered
empty query is NOT inserted between consecutive occupied natural dates.
Take Hausdorff limits E,T_*. A component of[0,c_*] minus E is the limit
of one old atom interval, with constant owner densities. Its only test
is its midpoint. Collapse that whole component to this test. The rest
of E outside T_* is null: each component of the complement of T_* can
contain at most one E point, since two distinct limiting endpoints would
force an old occupied midpoint between them. There are countably many
components. Retain the remaining finite cuts and send(c_*,1) to separate
Never. Reparametrize the first finite test as ROOT and the last as END.

This gives a compact ordered offered set T, isolated positive mixture
atoms, and zero mixture mass at every other test. END is empty. Testing
the raw interval(c_*,1), with error at most4|c_m-c_*| from its moving
boundary, proves the EXACT original Never identity

    P_i(Never)=lim_m P_i^m(Never).                  (C1)

For prescribed first-coalition kernels exclude ONLY the countably many
endpoints of positive limiting atom intervals, the finite/Never boundary,
and equal independent raw coordinates. The whole set E need not be null
and is NOT excluded. Two
remaining finite coordinates either lie in the SAME positive limiting
old interval and are eventually tied, or have a retained endpoint
strictly between them and are eventually correctly ordered. Thus all
coalition indicators converge almost everywhere and in L1.

Products of the independent bounded densities converge weak-star:
first test rectangles, then their finite linear combinations, then
all L1 kernels by density and the uniform4^4 bound. Splitting each
integral into its changing-kernel L1 error and fixed-kernel weak-star
limit proves convergence of every coalition probability and U. This
uses no product of uncontrolled weak limits.

The SAME comparison-kernel argument applies to ANY moving old pure
query. Near an isolated positive limiting atom the query must be the
midpoint of the SAME whole old atom; no other offered query enters a
small endpoint-free neighborhood. At a nonatomic cut the equality set
has zero opponent mass. Literal Never has its separate kernel. Each
retained test is approached by old tests; old maximizing queries have
convergent subsequences. These two directions prove that stored B is
EXACTLY the maximum over all retained finite tests and Never, not a
maximum over a supplied subset. Responses are continuous on T: positive
atoms are isolated, and a nonatomic moving cut crosses vanishing mass.
Fubini gives U_i=integral V_i dP_i, justifying(U1) in this same carrier.

For general current owns s_i the exact retained endpoint correction is

    V_i(END)-V_i(Never)=s_i PRODUCT_(j!=i)N_j.      (C2)

At native owns zero this identifies END with Never. At a positive raised
table it prices Never separately; the two are not silently merged.
The proofs of Sections2--4 are identities and inequalities of these
retained ORIGINAL kernels. No modification, safe calendar compression
or unproved executable abstract clock is required. Degenerate points
with no positive finite tail make all every-cut claims vacuous or
immediate.

## 6. Native counterexample access and the uniform raised source

First, the required positive native absorbing infimum is available
from ANY hypothetical four-player UE counterexample; it is not an
unproduced strategic witness. If all original own singletons are
nonpositive, literal AllNever is already an exact uniform equilibrium.
Otherwise choose a positive own pivot s_m. The checked declarations

    normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
    all_punishmentNormal_of_normalCore_eq_univ

in the source files listed in Section9 give punishment-normal bounds
punishment_i<=s_i for every owner. Put b_m=0, b_i=s_i otherwise, and replace each
nonempty row entry by(r_i-b_i)/s_m, still keeping AllNever zero.
The exact single-pivot normalization gives own vector(1,0,0,0).
The checked reverse uniform-payoff lift under those punishment-normal
bounds shows this normalized game still has no uniform payoff.
Its full terminal-debt infimum is positive by the exact semantic
obstruction theorem; its absorbing infimum is therefore positive too.

Now subtract one from EVERY nonempty entry of the pivot recipient row.
Before and after this step all own singletons are nonnegative, so the
finite-response supremum contains Never. On every ABSORBING profile
both that recipient's prescribed payoff and its finite cap shift by
minus one, while other rows are unchanged. Hence absorbing debts are
preserved. The resulting native table Z has all owns zero and A>0.
This is NOT a row-affine invariance assertion at positive joint Never.
Changing native rewards by at most e changes every actual full SUM debt
and its absorbing infimum by at most8e; thus A>0 is relatively open.
No generic reward perturbation is needed for this packet.

Keep such a native Z fixed and let

    r_i(S)=theta_i[Z_i(S)+t], theta_i in[1/2,1], t>0,

on every nonempty coalition, with literal AllNever still zero. For two
forced finite replies the raise is constant, so EXACTLY

    Delta_i^r(x)=theta_i Delta_i^Z(x).            (12)

This is the only cancellation used in transferring END-cap hypotheses.
It does not assert affine invariance of delivered payoffs, debts or Never.

Native finite responses tend to native Never because owns are zero.
Thus their supremum already contains literal Never; the corresponding
retained statement follows from(C2). Both actual profiles and H_r give

    B_i^r=theta_i(B_i^Z+t),
    U_i^r=theta_i[U_i^Z+t(1-nu)],
    d_i^r=theta_i[d_i^Z+t nu].                    (13)

Here the prescribed raise keeps its ORIGINAL all-Never correction.
The native U,B,N of an H_r point are recovered by these identities and
are also original native closure data of its actual realizing sequence.

At an original raised SUM minimum, AllNever gives D_r<=t SUM theta<=4t,
hence D_Z<=8t. Move an owner with smallest Never mass n<=nu^(1/4) to
one finite clock. The result ACTUALLY absorbs. Coupling changes four
prescribed values and three opponent caps by at most2Mn each; the
mover's cap is unchanged. Therefore, first for actual profiles and then
their original augmented limits,

    A<=D_Z+14M nu^(1/4).                           (14)

For0<t<A/16 this proves the ORIGINAL uniform collar

    nu>=(A/(28M))^4>0.                             (15)

Every marginal Never mass is at least this product. These coordinates
are retained by(C1). The raised full infimum is itself positive: a
sequence with D_r->0 would force both D_Z->0 and nu->0 by(13), contrary
to(14). Thus these are genuine positive original-minimum sources, not
a minimum of a restricted law class or a minimum suffix.

Apply Section4 at EVERY offered x of this same original representation.
It gives(B2) and a uniform every-cut obstruction to dominance on scales
larger than t. Whenever all three observers of h are END-active, (12)
also transfers those cap comparisons exactly and Section2 gives the
stronger scale-free inequality(4), with the uniform collar(15).
An entirely isolated positive late stream has T_h=0 and is excluded
under those observer caps, however small its mass is relative to t.
Asymptotic dominance in three/four-future END-active configurations is
likewise excluded without a contact, geometric or finite-support premise.

This does not assert that all original minima have three observer END
caps. It proves a strict reduction of that exact source class and a
universal every-cut necessary inequality for all the other cap modes.

## 7. Exact full sixty-coordinate multifinite control

The following rules assign EVERY native recipient/coalition entry:

    Z_i(S)=0     if i belongs to S;
    Z_i(S)=-1    if i does not belong to S and |S|=1;
    Z_i(S)=100   if i does not belong to S and |S|>=2.  (F1)

Owns are zero, M=100, ALL participant pairs and grand rewards are zero,
and passive triples are100. The latter cannot be silently dropped.
At the only occupied finite date1, take masses

    P_0(1)=1/2, P_j(1)=1/200 for j=1,2,3,
    P_i(Never)=1-P_i(1).

ROOT0 and empty END2 are offered tests. At query x=1,

    R_0=mu_0=1/2, T_0=3/200, z=1,
    nu=199^3/16000000=7880599/16000000.             (F2)

Every finite ROOT or LAST response of any owner pays zero, since its
quitting coalition contains that owner. Its END response pays the
passive reward against the other three complete laws. Those exact values
are

    END_0=-59003/8000000,
    END_j=1/80000 for j=1,2,3.                    (F3)

Thus h=0 is END-INACTIVE and all three observers are strictly END-active,
as allowed. Native prescribed and full-cap vectors are

    U=(-59003,199,199,199)/16000000,
    B=(0,200,200,200)/16000000,
    D_Z=29503/8000000.                            (F4)

For each observer j!=0 the exact one-finite sum in(7) is

    -39999/80000,

where its h term is -39601/80000 and the two other single-finite terms
are each -199/80000. The multifinite remainder is EXACTLY1/2, since
the probability of at least two finite opponents is1/200 and its
payoff difference is100. The result is Delta_j=1/80000, as in(F3).
Dropping that remainder would give the WRONG SIGN for END activity.

The solo-h observer debt at z=1 is3: all three Gamma=-1 and J=0.
This is consistent with the loose quantitative bound in(3); other
finite tails here are small but not zero. If their mass e were sent to
zero at this FIXED table, each observer END value would be

    -1/2+e^2/2+100e,

which becomes negative. Thus one cannot keep these three END caps while
letting the ratio T_0/R_0=6e tend to zero.

The table honestly has A=0: players0 and1 surely quit at date zero and
players2 and3 choose Never, giving an absorbing exact Nash with payoff
(0,0,100,100). Either active player who continues receives passive -1;
an observer who joins receives0 instead of100. All other finite and
Never responses are the same passive values. This control checks the
complete expansion, full menus, signs and allowance for h END-inactivity;
it is not a positive-A example or an original minimum.

## 8. Full-table boundaries: a missing END cap and zero hazard

Here is a second COMPLETE sixty-entry native table. Row0 is zero.
The only nonzero entries in all other rows are

    Z_1(0)=1, Z_1(01)=2;
    Z_2(0)=-1, Z_2(02)=-2;
    Z_3(03)=2.                                    (F5)

EVERY other entry is zero. Let player0 have mass2^(-m-2) on every
natural date m>=0 and original Never mass1/2; all observers use Never.
Every natural date, INCLUDING ROOT, is occupied. Players1 and2 have
every finite/Never response equal respectively1/2 and-1/2, so their
END caps are active and cofinal. Player3 has

    V_3(m)=2^(-m-1), V_3(END)=V_3(Never)=0,

and ENTIRE cap ROOT alone. Its native vectors are
U=(0,1/2,-1/2,0), B=(0,1/2,-1/2,1/2), D_Z=1/2, nu=1/2.
For h=0 the other tails vanish, T_h=0, but the middle quantity in(3)
at the read hazard z=1/2 equals1. Thus its zero upper bound cannot be
asserted after omitting that third observer's END premise. Every
sure-solo-h geometric clock has debt
|2z-1|+2z>=1, so neither an exact nor a vanishing-debt solo family
follows from only two observer inequalities. The unrestricted debt
bound(B1) is not contradicted: its left side contains that observer's
positive deficit. AllQuit is an exact native absorbing Nash0 because
grand and withdrawal triples are zero. No positive-A control is claimed.

A third full table has ONLY Z_1(01)=2,Z_2(0)=1,Z_3(0)=1 nonzero;
EVERY other entry is zero. Actual player0 laws put mass1/(2n) on
each of0,...,n-1 and mass1/2 on original Never, with all observers
Never. Exact native vectors are

    U=(0,0,1/2,1/2), B=(0,1/n,1/2,1/2), D_Z=1/n.

The rescaled original uniform-clock limit on[0,1] has finite nonatomic
mass1/2, original Never mass1/2, empty END1, mu_0(x)=0 and R_0(x)>0
for every x<1. ALL observers are END-active, including the first
observer's flat zero native cap. The z read at such a query is ZERO.
No positive-hazard solo-0 clock is exact Nash, because observer1 can
gain2z. Nevertheless the actual clocks of Section3 have exact debt2z
and fixed payoff(0,0,1,1), so the all-error absorbing conclusion holds.
AllQuit is again exact native Nash0. This control forbids replacing
the scalar z=0 argument by an asserted actual absorbing zero-rate law.

## 9. Exact source interfaces, overlap and Lean handoff

The following nine tracked source files provide the complete native
counterexample access and original semantic correspondence used above:

* `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
  in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`
  gives full normal core for an actual four-player no-UE hypothesis.
* `all_punishmentNormal_of_normalCore_eq_univ` in
  `UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean`
  gives the all-player punishment-normal bounds.
* `quittingSoloReward_singlePivotNormalized` in
  `UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean`
  gives the normalized own vector.
* `isUniformEquilibriumPayoff_original_of_singlePivotNormalized` in
  `UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean`
  supplies the reverse lift under positive pivot and those bounds.
* `quittingTerminalSemanticCarrier` and
  `exists_terminalProfile_sequence_tendsto_semanticPair` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`
  give the actual semantic closure and its realizing sequences.
* `quittingTerminalSemanticDebtSum` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticDebt.lean`
  is the full continuous SUM functional.
* `quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum`
  and
  `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
  in `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`
  identify the minimum with the actual full infimum and its no-UE
  obstruction; the finite player type here is inhabited.
* `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff`,
  `quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`,
  `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
  and
  `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
  in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`
  identify independent complete-law integration and replacement caps
  with actual payoff and unrestricted behavioral deviation caps.
* `quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
  `UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`
  gives the finite-END versus literal-Never limit and the own correction.

The raw solo-rate criterion is ALREADY implemented for general finite
player sets: `isUniformEquilibriumPayoff_soloReward_of_inactive` and
`isεAsymptoticNash_soloStationary_exact_iff` in
`UniformEquilibrium/Quitting/Punishment/OwnerSoloCertification.lean`.
It assumes nonnegative owner solo reward and exactly the inequalities
(1-z)s_i+z R_i(ih)<=R_i(h). This packet claims no new raw solo existence
class. Section3 reproduces its elementary native full-cap calculation
including scalar continuity at zero, because the output must be ACTUAL
and absorbing and the proof must not depend on a supplied rate.

The NEW contribution is the original all-coalition expansion(7), its
conversion into(3) from ENTIRE END caps, and the unrestricted every-cut
bound(B1) from actual Never deficits. These turn original data into the
already certified scalar consumer. The complete dominant late-tail
exclusion includes three-/four-cofinal-stream sources without a contact
producer. It is distinct from a TOTAL-future-mass bound varying a single
ROOT split, and from a conditional two-future geometric-calendar argument.
No result about the completeness of a bounded controller class is used.

Formalization should first partition the three opponent draws for literal
natural clocks and prove(7) uniformly over every query. Bound the
multi-finite event by the three pair events; do not omit forced triple
or grand outcomes. Prove the native solo exact debt at positive hazards
and its continuous scalar endpoint. Then(9),(3) and(U1)--(B1) follow
from inequalities and original Fubini, with no stationarity or IFT.
The original retained representation and Native Never collar can be
formalized independently; the nine checked source interfaces must keep
their actual quantifiers and positive-pivot hypotheses.

Exact tests should include the FULL sixty rules in Section7, especially
the positive multifinite remainder1/2 opposing a negative single-finite
sum, the END-inactive owner h, and every ROOT/LAST/END/Never menu.
Section8 separately checks the essential all-observer END hypothesis
and the scalar zero-rate boundary. No Lean implementation, refactor,
new trust assumption or unrun build is prescribed.

The surviving source may have two or more comparable late streams,
END-inactive observers with positive cap deficits, or both. Neither
every-cut inequality asserts finite support, periodicity, cofinal
cap exhaustion or a strategy-class completion. A global consumer of
those remaining balanced configurations is still needed. The full
four-player quitting-game UE conjecture remains open.

