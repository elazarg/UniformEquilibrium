# One-sided pair signs force uniform three-owner dispersion

This is ordinary mathematics to be formalized. No new Lean declaration
or implementation is claimed. The finite-quitting conjecture remains open.

## 1. Exact theorem and source scope

There are four independent private complete stopping laws on the natural
dates and a separate literal Never. All whole-law unilateral replacements
are allowed. Native live, own-singleton and all-Never rewards are zero.
Fix ONE finite reward table Z, put M=max(1,max|Z_i(S)|), and write

    U_i=prescribed payoff, B_i=complete response supremum,
    e_i=literal Never response, d_i=B_i-U_i, D=sum_i d_i,
    N_i=ORIGINAL Never mass, f_i=1-N_i, beta=sum_i f_i,
    epsilon=f_(3)+f_(4), f_(1)>=f_(2)>=f_(3)>=f_(4),
    A=inf{D(P):P actual and product_i N_i(P)=0}.

Let Gamma_ij=Z_i({j}) and J_ij=Z_i({i,j}) for i!=j. Assume A>0,
every off-diagonal Gamma entry is nonzero, and EVERY unordered pair
{i,j} has an orientation (i,j) satisfying

    Gamma_ij (Gamma_ij-J_ij)>0.                       (PAIR)

Then there is an explicit c=c(Z,A)>0 such that EVERY actual profile has

    D+beta epsilon >= c beta^2.                      (DISP)

The same inequality holds on the original augmented compact carrier,
by continuity of D,N and the order statistics f_(k). Thus every nontrivial
native zero-debt point satisfies epsilon>=c beta and
f_(3)>=c beta/2. Every conditional suffix of an ACTUAL positive-N
zero-debt source satisfies the same conclusion, with its own conditional
finite masses. No suffix is assumed minimizing.

The literal fixed13 family satisfies (PAIR) whenever A>0, as proved in
Section 5. No recipient row-distinctness, reciprocal pair guard,
genericity of the 31 free entries, source minimization or finite calendar
bound is required. All constants may depend on the fixed finite free
completion; no uniformity over unbounded or near-boundary completions is
asserted.

The conjecture-facing change is exclusion of normalized one-/two-owner
mass concentration at native zero debt, and at original raised full-SUM
minima whose total finite mass dominates the raise. The literal fixed13
corollary applies despite exact row equalities which violate earlier
generic hypotheses: for example recipient 1 has both own-singleton and
03 reward zero. No raw reward-table UE class is closed by this result.
The source hypotheses A>0, native zero debt, or raised globality are
used only where explicitly stated; no strategic witness is assumed.

## 2. Exact pair separation without compactifying a calendar

Fix an unordered pair and choose its orientation in (PAIR). For any two
independent SURE FINITE laws F_i,F_j on the SAME original calendar put

    a=Pr(T_i<T_j), b=Pr(T_j<T_i), z=Pr(T_i=T_j),
    a+b+z=1.

All other owners use Never. Never minus the prescribed response averaged
under F_i is

    L_i=Gamma_ij a+(Gamma_ij-J_ij)z,
    L_j=Gamma_ji b+(Gamma_ji-J_ji)z.                  (L)

Indeed a prior opponent stop gives the same passive reward under Never
and the finite response; an own earlier stop loses Gamma; a tie replaces
Gamma by J. This argument prices the original dates and ties exactly.

Define

    m_ij=min(|Gamma_ij|,|Gamma_ij-J_ij|)>0,
    g_ij=|Gamma_ji|>0, h_ij=|Gamma_ji-J_ji|,
    delta_ij=g_ij m_ij/(m_ij+g_ij+h_ij)>0,
    delta=min_(unordered pairs) delta_ij>0.          (DELTA)

The two coefficients in L_i have the same sign by (PAIR), so
|L_i|>=m_ij(a+z). If k=max(|L_i|,|L_j|), then

    a+z<=k/m_ij,
    g_ij b<=|L_j|+h_ij z<=k+h_ij k/m_ij.

Adding and using b=1-(a+z) gives

    g_ij<=k[1+(g_ij+h_ij)/m_ij],
    max(|L_i|,|L_j|)>=delta_ij>=delta.               (SEP)

Thus no finite-calendar, infinite-calendar, geometric, diffuse or retained
pair chronology can make BOTH integrated active Never gaps vanish.
Neither a cap nor a Nash assertion about the isolated pair was used.

## 3. Original debt controls the normalized pair errors

For an arbitrary actual profile with f_i>0, let pbar_i be the payoff of
its own normalized finite response law F_i, against its ORIGINAL
opponents. Complete-law Fubini gives

    d_i=N_i(B_i-e_i)+f_i(B_i-pbar_i).                (FUB)

Both terms are nonnegative. If N_i>0 then

    |e_i-pbar_i|<=d_i/N_i+d_i/f_i.                  (GAP)

This estimate is valid for either sign of e_i, pbar_i, or any payoff.
No zero response before the first date is inserted.

Retain the laws of the two largest finite owners i,j and censor the
remaining finite masses epsilon to their OWN Never labels, obtaining Q.
Coupling changes each fixed response by at most 2M epsilon. Applying this
to Never and to the SAME normalized own finite response gives

    |(e_i-pbar_i)(Q)-(e_i-pbar_i)(P)|<=4M epsilon.

In Q the exact scaling identity is

    (e_i-pbar_i)(Q)=f_j L_i,
    (e_j-pbar_j)(Q)=f_i L_j.                        (SCALE)

The opponent-Never branch pays own singleton zero under both response
laws. Therefore, whenever both original N_i,N_j are positive,

    |L_i|<=D/(N_i f_j)+D/(f_i f_j)+4M epsilon/f_j,
    |L_j|<=D/(N_j f_i)+D/(f_i f_j)+4M epsilon/f_i.  (ERR)

All errors are charged to ORIGINAL debt D. Censored debt is never
substituted in this normalized estimate.

## 4. Explicit proof of the global inequality

Censoring total finite mass e changes total debt by at most 14M e:
four prescribed payoffs cost at most 8M e, and three opponent caps for
each moved owner cost at most 6M e. Caps are controlled uniformly over
whole responses before taking the supremum.

If only one owner h has finite mass f_h, normalize its finite part to a
sure finite law on the SAME dates. The resulting actual profile absorbs.
Owner h's payoff and cap are zero; every other owner's payoff and every
response scale by f_h, because own-singleton and all-Never rewards are
zero. Hence the one-owner profile has debt at least A f_h. Censoring
all except the largest owner therefore gives

    A f_(1)<=D+14M(f_(2)+epsilon),
    (A+14M)(f_(2)+epsilon)>=A beta-D.               (ONE)

Put

    r=A/(A+14M), b=r/4,
    eta=(A/(28M))^4,
    C_D=b^(-2)+4/(eta b), C_E=4M/b,
    c=min(A/32, r/4, delta/max(C_D,C_E))>0.         (CONST)

An arbitrary absorbing profile has D<=8M, so 0<A<=8M and eta<1.
The beta=0 case is immediate. Otherwise beta<=4. There are four cases.

If D>=A/2, then D>=A beta^2/32. If D>=A beta/2, then
D>=A beta^2/8. Both imply (DISP) with (CONST). Hence assume

    D<A/2, D<A beta/2.                             (SMALL)

Move the least original Never mass to one finite date to force actual
absorption. The same coupling count gives

    A<=D+14M nu^(1/4), nu=product_i N_i.

Thus (SMALL) implies nu>=eta and EVERY original N_i>=eta. This is the
only Never collar used, and it is produced from A and original debt.

Equation (ONE) and D<A beta/2 imply
f_(2)+epsilon>r beta/2. If epsilon>=r beta/4, then
beta epsilon>=r beta^2/4, again proving (DISP). Otherwise

    f_(2)>r beta/4=b beta,
    f_(1)>=f_(2)>b beta.

Use (ERR), N_i>=eta, beta<=4, and (SEP) for this largest pair. They give

    delta<=D/(b^2 beta^2)+D/(eta b beta)
                              +4M epsilon/(b beta)
          <=C_D D/beta^2+C_E epsilon/beta.

Multiplying by beta^2 proves
delta beta^2<=C_D D+C_E beta epsilon, and hence (DISP) with (CONST).
All cases are exhausted. No limiting extraction or shared-clock
compactification was needed for the actual theorem.

For small TOTAL mass beta<=1/2 one can replace C_D by b^(-2)+b^(-1)
and omit eta, since all N_i>=1/2. The preceding global constant is
retained for a single statement covering every profile.

## 5. All six literal fixed13 pairs

It suffices to assume the following subset of the literal fixed13 data:

    Gamma=[0,-2,-5,4; -6,0,-4,6; 1,3,0,-5; 1,-1,4,0],

participant rewards of owners 1,2 nonpositive, and these six fixed
participant entries:

    J01=-1, J03=3, J10=-7, J13=-1, J30=2, J31=-2.

The remaining entries may be arbitrary finite reals subject to those
participant signs. In particular all literal fixed13 completions are
included, without needing its fixed triple or passive-pair entries.

First A>0 forces J23>-5. If J23<=-5, let owner 3 Quit surely at date
zero and every other owner use Never. Owner 3 has payoff and cap zero;
owners 0,1,2 have passive values 4,6,-5. Their date-zero joining values
are 3,-1,J23, respectively, all no larger than those passive values.
All later dates and literal Never earn the passive values. This is an
actual absorbing full Nash profile, contradicting A>0. As owner 2 has
nonpositive participant rewards, it follows that -5<J23<=0.

Choose orientations and the exact constants as follows:

| Pair | Orientation | Same-sign coefficients Gamma, Gamma-J | delta_ij |
| --- | --- | --- | --- |
| 01 | (0,1) | -2,-1 | 3/4 |
| 02 | (2,0) | 1,1-J20>=1 | 5/(6+|-5-J02|) |
| 03 | (0,3) | 4,1 | 1/3 |
| 12 | (2,1) | 3,3-J21>=3 | 12/(7+|-4-J12|) |
| 13 | (1,3) | 6,7 | 3/4 |
| 23 | (2,3) | -5,-5-J23<0 | 4(5+J23)/(9+J23+|4-J32|) |

Every denominator is positive and finite, and every numerator is
strictly positive. Thus their finite minimum delta is positive. This
verifies every hypothesis of Sections 1-4 for EVERY finite free
completion satisfying the literal signs and A>0.

## 6. Original carrier, actual suffixes, and global-minimum consumers

The original augmented carrier is the Euclidean closure of actual
(U,B,e,N). The actual inequality (DISP) depends only on the continuous
coordinates D and N, including the continuous order statistics of
1-N_i. It therefore extends to that carrier.

For an ACTUAL native zero-debt source with original N_i>0, take any
whole-date survival cut and set s_i=N_i+R_i>0, where R_i includes the
whole current atom. The independent conditional laws are actual laws
on the translated natural calendar. To test any conditional deviation,
copy the old own law before the cut and replace its conditional law on
own survival. The gain over the original prescribed payoff equals
product_i s_i times the conditional gain: all earlier absorption events
cancel. Thus the conditional full debt is at most D/product_i s_i=0.
Applying (DISP) gives

    f_(3)(cut)>=c beta_cut/2                         (TAIL3)

at EVERY nontrivial actual conditional suffix. Conditioning at a positive
atom retains that WHOLE atom and creates no response before suffix date
zero. No tail inherits an objective minimum.

If original N_i>=n0>0 and R_i are original inclusive finite tails at an
old cut, then f_i(cut)=R_i/(N_i+R_i), and R_i>=n0 f_i(cut).
Since beta_cut>=sum_i R_i, (TAIL3) yields at least three distinct owners
with

    R_i >= (n0 c/2) sum_j R_j.                      (ORIG3)

Consequently every actual positive-N native zero-debt source in this
class has three uniformly macroscopic finite tails at every nontrivial
cut. If exactly
three owners have unbounded finite support, those three terminal tails
are uniformly comparable after the remaining owner's last finite date.

At original raised global minima for fixed theta>0, r_i(S)=theta_i[Z_i(S)+t],
put Theta=sum_i theta_i and K=Theta/min_i theta_i. A forced finite
response gains exactly theta_i t under this raise. Its native late-date
limit equals e_i because own-singleton is zero; the raised Never
response is no larger than theta_i(B_i+t). Hence, on actual profiles
and by continuity on the augmented carrier,

    B_i^raised=theta_i(B_i+t),
    U_i^raised=theta_i[U_i+t(1-nu)],
    sum_i d_i^raised=sum_i theta_i d_i+t Theta nu.

At a global minimum of THIS full raised SUM objective, the AllNever
comparison gives sum_i theta_i d_i<=t Theta(1-nu)<=t Theta beta.
Thus D<=K t beta, and (DISP) gives

    epsilon>=c beta-Kt,
    beta<=2Kt/c OR f_(3)>=c beta/4.                 (RAISED)

This uses the same original global objective, not optimization of a
conditional suffix. No all-END or collision-selection hypothesis is
needed. The carrier statement covers compact minima not attained by
one actual law.

## 7. Boundary tests

For the pair lemma, take Gamma_ij=Gamma_ji=1 and J_ij=J_ji=0.
Then L_i=a+z and L_j=b+z, so max(|L_i|,|L_j|)>=1/2 for every
timing triangle. Formula (DELTA) gives the valid lower bound 1/3.

For the GLOBAL inequality, A>0 is essential even with all strict pair
orientations. On four owners define Z_i(S)=1 when S={j} with j!=i,
and zero otherwise. All own singleton entries vanish, all off-diagonal
Gamma entries are 1, and all J entries are zero, so (PAIR) holds for
every pair. Let only owner 0 Quit surely at date zero. Then
U=B=(0,1,1,1), D=0, beta=1 and epsilon=0. The profile absorbs, so A=0.
Thus no positive constant in (DISP) is possible after dropping A>0.

Strictness cannot be removed from the pair lemma. With both Gamma and
both J equal to 1, and both sure finite laws the same point mass,
a=b=0,z=1 and L_i=L_j=0. With own rewards zero this two-owner table
also has an absorbing Nash profile in which only one owner quits;
A=0 honestly, so this is a boundary test, not an A>0 source falsifier.

The nonzero reverse Gamma is also needed by the pair lemma: take
Gamma_ij=1,J_ij=0,Gamma_ji=J_ji=0 and i strictly later than j.
Then a=z=0,b=1 and both integrated gaps vanish despite the forward
strict orientation.

For the literal pair23 guard, J23=-5 is exactly the boundary where
the displayed pure3 absorbing Nash profile becomes available. As
J23 decreases below -5 it remains Nash. The positive constant in
(DELTA) may tend to zero as J23 decreases to -5 from above; no
uniform radius over that boundary is asserted.

## 8. Source correspondence and Lean handoff

The exact behavioral/law correspondence inspected is
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`:
for a finite nonempty player set, every supplied complete law profile's
replacement cap equals the unrestricted behavioral best-response value
of its conditional-hazard realization. Its companion
`quittingBehaviorStoppingLaws_stoppingLawProfile` reconstructs all
original laws exactly. The same file's
`abs_quittingStoppingLawReplacementPayoffCap_sub_le_opponents` supplies
uniform opponent-law continuity; the finite censorship estimates above
give its direct coupling specialization.

The positive semantic endpoint remains
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The negative endpoint is
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.
Neither endpoint alone supplies A>0: A is the absorbing native SUM
infimum, which is the explicit source hypothesis of this theorem.
Native AllNever itself has zero full debt because all own singletons
are zero. Thus A>0 is not native nonexistence of an equilibrium; it
restricts absorbing approximations at the native table. Applications
to a raised or normalized conjecture source must supply this distinct
absorbing-gap premise by their own source reduction.

The bounded source search found no equivalent implemented one-sided
orientation dispersion theorem. This packet's new mathematical content
is the finite timing-triangle bound and its direct original-debt
consumer, with no geometric normalized-pair or row-distinctness input.
The six-entry literal corollary gives actual scope beyond hypotheses
which would fail at its fixed repeated row values.

Formalize (SEP) first as finite real algebra on a+b+z=1. Then formalize
(FUB), same-calendar finite normalization, the original-debt gap estimate,
and the censorship scaling (SCALE). The all-profile theorem has the
explicit hypotheses A>0, nonzero off-diagonal Gamma and one strict
orientation per unordered pair, and conclusion (DISP) with (CONST).
Retain Never coordinates in the compact carrier; the extension is a
finite-dimensional continuity argument. The raised-minimum consumer
uses full SUM debt of the exact same raised table. No requested
conclusion belongs as a structure field.

The result is a source-class exclusion, not a new equilibrium producer.
It leaves the beta=O(t) raised branch and the three-/four-owner dispersed
branch open. It does not prove common triple collisions, collision-graph
connectivity, or exclusion of all proper cofinal triples. No new Lean
build or axiom audit was run for this ordinary mathematical proof.
