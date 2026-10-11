# A nonconvex full-cap chamber for the four-active K10 table

Status: ordinary complete proof candidate, UNREVIEWED and not Lean-checked.
No export or unrestricted finite-quitting conjecture conclusion is claimed.
The stated conclusion is uniform-equilibrium existence for the ONE literal
four-player table below. The new proposed step is a table-specific invariant
cap chamber, not the already checked cap-Nash debt-scaling identity. The
argument optimizes over the closed actual semantic carrier; it does not
assume continuity of an equilibrium selector, convexity of independent
laws, or convergence of one exact-root chronological spine.

## 1. Self-contained question and conclusion

Players are I=Z/4Z. Live and Never rewards are0. At the first finite quitting
date the nonempty quitting coalition S receives the following vector:

    singleton{i}: 1 to i, 4 to i+2, 0 to its two neighbors;
    adjacent pair{i,i+1}: -1 to i, 2 to i+1, 1 to outsiders;
    opposite pair: 0 to its members, 1 to outsiders;
    triple: -1 to its three members, 10 to its outsider;
    grand coalition: 9 to every player.                    (1)

All arithmetic on labels is modulo4. Prescribed complete private clocks
are independent, with values in Nat union{Never}. Every unilateral response
is an unrestricted complete behavioral replacement, equivalently an
independent private date-or-Never law on the sole unabsorbed history.

Question. Can a NONCONVEX chamber in the actual prescribed-payoff/FULL-cap
carrier force a diagonal, without selecting a persistent exact-root spine?

Claim. There is a fixed vector v and a sequence of actual independent
behavior profiles p_n such that their prescribed terminal payoffs tend to v
and EVERY complete unilateral terminal gain is at most epsilon_n, with
epsilon_n->0. Consequently v is a uniform-equilibrium payoff for(1).
An exact terminal Nash profile, a stationary equilibrium, an explicit
calendar, a convergence rate, and a theorem for arbitrary raw tables are
NOT asserted.

## 2. Actual semantics and the known cap-Nash cancellation

For an actual profile p let U_i be its terminal payoff and B_i its supremum
over ALL complete unilateral replacements. Set

    d_i=B_i-U_i,       D=max_i d_i.

Always d_i>=0. For(1), B_i>=0: the legal Never response receives only
passive rewards0,1,4,10, or Never0. Also -1<=U_i<=10 and0<=B_i<=10.
Let S be the closure in R^8 of ALL actual pairs(U,B). It is nonempty and
compact, inherits these inequalities, and is invariant under EVERY product
root prefix. No convexity of S is claimed or used.

At a root q in[0,1]^4, define

    c=product_i(1-q_i),   alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(A union{i})],
    b_i=E[r_i(A)*1_(A nonempty)],

where A is the independent opponent quitter set at that root. Exact FULL
semantic prefixing is

    U_i'=q_i*Q_i+(1-q_i)*(b_i+alpha_i*U_i),
    B_i'=max{Q_i,b_i+alpha_i*B_i}.                       (2)

The stage game with continuation B pays r(A) upon a nonempty root quit
set and B upon all Continue. If q is ANY mixed Nash equilibrium of this
finite two-action game, then each player's mixture attains the maximum
of its two endpoints. Thus

    B_i'=q_i*Q_i+(1-q_i)*(b_i+alpha_i*B_i),
    d_i'=c*d_i,           D'=c*D.                       (3)

Finite mixed Nash existence is unconditional. Equations(2)--(3) use full
caps, not individual best replies against prescribed continuation U, and
are valid even if a cap supremum is not attained.

## 3. Every exact cap-Nash root preserves a cap chamber

Proposition. For EVERY continuation B in[0,infinity)^4 and EVERY exact
mixed Nash root q against B, with B' as in(2),

    min_i B_i<=1  ==>  min_i B_i'<=1,                  (4)
    sum_i B_i'-4 >= c*(sum_i B_i-4).                  (5)

There is NO upper-bound assumption on B in this proposition. These are
statements for the ENTIRE root-Nash correspondence, not one selected root.

### 3.1. No sure root, for any continuation

Suppose player i quits surely. Opposite i+2 has joining-minus-Continue
differences -4,-2,-1 according as zero, one, or two of the other
nonowners quit. It strictly Continues. Predecessor i-1 then has joining
differences -1 or-2 according as successor i+1 Continues or Quits, so also
strictly Continues. The successor strictly joins for2 rather than0.
Owner i now receives-1 and can withdraw for0. This contradicts Nash.
The argument does not use continuation payoffs, since another sure
quitter prevents all Continue on each relevant comparison.

Hence every root coordinate is strictly below1. Every positive coordinate
is therefore interior and its Quit and Continue endpoints agree.

### 3.2. Support of size one or two

A singleton-support root owned by i has B_i'=Q_i=1. Its absorption rewards
have total5.

For an adjacent active pair q=(a,b,0,0), rotated as necessary, the two
active endpoint equalities give

    B0=(1-2*b)/(1-b),        B1=(1+a)/(1-a),
    B0'=1-2*b<1.                                      (6)

Input nonnegativity forces b<=1/2. For an opposite active pair
q=(a,0,b,0), the equalities give

    B0=(1-5*b)/(1-b),        B2=(1-5*a)/(1-a),
    B0'=1-b<1.                                        (7)

Thus a,b<=1/5 in this opposite case. All these formulas concern stage
Nash against B, not a stationary Nash assumption.

### 3.3. Support of size three

Rotate the missing label to3 and write q=(a,b,e,0), all a,b,e positive.
The relevant exact raw endpoints are

    Q0=1-2*b-e+b*e,       b0=(4-3*b)*e,
    Q2=1-a+b-2*a*b,       b2=(4-3*b)*a.

Consequently active equality and B>=0 imply

    1-2*b-5*e+4*b*e>=0,
    1-5*a+b+a*b>=0.                                  (8)

In particular b<=1/2, a<=(1+b)/(5-b)<=1/3, and

    e<=(1-2*b)/(5-4*b)<=(1-2*b)/3.

The total root hazard therefore satisfies

    a+b+e<=2/3+b/3<=5/6.                             (9)

Also B0'=Q0<1. This proves the required low-cap output for every triple
support, without assumptions on the inactive player's endpoint.

### 3.4. Full support

Put z_i=q_i/(1-q_i)>0 and, for recipient i,

    x=z_(i-1),   y=z_(i+2),   w=z_(i+1),
    T=x*y+x*w+y*w,       V=x*y*w.

Multiplying Quit and the opponent-stop term by product_(j!=i)(1+z_j)
gives respectively

    P_i=1+2*x-w-T+9*V,
    N_i=4*y+T+10*V.

Because alpha_i=1/product_(j!=i)(1+z_j), active equality is

    B_i=P_i-N_i=1+2*x-w-4*y-2*T-V.                   (10)

Let Z=sum_i z_i, E2=sum_(i<j)z_i*z_j and
E3=sum_(i<j<k)z_i*z_j*z_k. Summing(10) yields

    0<=sum_i B_i=4-3*Z-4*E2-E3,
    Z<=4/3.

By concavity of z/(1+z),

    s:=sum_i q_i<=4*(Z/4)/(1+Z/4)<=1.                (11)

Direct enumeration in the ORIGINAL probability coordinates also gives

    sum_i Q_i-4=-2*s-Aq-2*Oq+12*E3q,                (12)

where Aq=sum_i q_i*q_(i+1), Oq=q0*q2+q1*q3, and
E3q is the elementary degree-three symmetric sum. Maclaurin's elementary
bound E3q<=s^3/16 and(11) imply

    sum_i B_i'-4=sum_i Q_i-4<=-2*s+(3/4)*s^3<0.

Hence at least one output cap is strictly below1. Together with the
smaller supports and the unchanged all-Continue root, this proves(4).

### 3.5. Total-cap surplus

Write P1,P2,P3,P4 for the probabilities of exactly one, two, three, four
quits at this root, and split P2=P_adj+P_opp. The total reward of(1) is
5 on singletons,3 on adjacent pairs,2 on opposite pairs,7 on triples,
36 on the grand coalition. Since stage Nash identifies B' with the
on-policy stage payoff,

    sum B'-4=c*(sum B-4)+H(q),
    H=P1-P_adj-2*P_opp+3*P3+32*P4.                  (13)

We show H>=0 for EVERY Nash root at B>=0.

An elementary Poisson-binomial fact is useful. If all q_i<1 and
sum_i q_i<=1, then P1>=2*P2. Indeed, with z_i=q_i/(1-q_i),

    sum q_i=sum z_i/(1+z_i)
       >=Z^2/(Z+sum z_i^2).

This is Cauchy--Schwarz; zero z_i are omitted. If sum q_i<=1, it gives
2*E2=Z^2-sum z_i^2<=Z. Multiplication by c gives
2*P2<=P1. The all-zero case is immediate.

For opposite, triple, and full supports, the bounds(7),(9),(11) give
sum q_i<=1. Thus

    H=(P1-2*P2)+P_adj+3*P3+32*P4>=0.

For an adjacent pair, (6) gives b<=1/2 and

    H=a+b-3*a*b>=0.

If b<=1/3 this is immediate; otherwise its minimum over0<=a<=1 is
1-2*b>=0. For a singleton H=q_i>=0; all Continue gives H=0.
This completes(5) and the proposition.

## 4. A literal actual full-cap seed

Let players0,2 Never. Independently, each of players1,3 Quits at date0
with probability1/2 and otherwise Never. Exact actual values and FULL
caps are

    U=(1/4,5/4,1/4,5/4),
    B=(1/2,5/2,1/2,5/2),
    D=5/4,       sum B-4=2.                          (14)

For player0 or2, Never and Quit0 each pay1/4, whereas EVERY positive
finite deadline pays1/2. For player1 or3, Quit0 pays1/2, Never pays2,
and EVERY positive finite deadline pays5/2. These exhaust the pure
date-or-Never responses; arbitrary independent response laws are their
mixtures. Thus(14) uses actual unrestricted caps, not sampled deadlines
or supplied cap annotations. No triple or grand reward is encountered.

## 5. Compact chamber minimization gives a diagonal

On the actual semantic carrier S of Section2 consider the CLOSED set

    K={(U,B) in S: min_i B_i<=1,
                       sum_i B_i-4>=(8/5)*D(U,B)}.    (15)

It is compact and nonempty by(14). It is not claimed convex. EVERY
exact Nash prefix against the point's FULL cap B preserves K: (4)
preserves the low-cap condition, and(3),(5) give

    sum B'-4>=c*(sum B-4)>=(8/5)*c*D=(8/5)*D'.

The new point remains in S by continuity of the literal prefix map and
actual-profile prefix invariance. These facts apply at carrier limits;
no cap-Nash selector continuity or approximating sequence of exact Nash
roots is needed.

Let (U*,B*) minimize D on K. Suppose its minimum D*>0. Then
sum B*>4 and min B*<=1. There is a NONZERO exact Nash root against B*:

* If min B*<1, all Continue is not Nash. Finite mixed Nash existence
  supplies a nonzero root.
* Otherwise every cap is>=1, at least one is exactly1, and at least one
  exceeds1. Choose i with B_i*=1 and B_(i+1)*>1; such an edge exists
  around the four-cycle. Let only i Quit with probability

      0<p<min{1,(B_(i+1)*-1)/(B_(i+1)*+1)}.

  Owner i is indifferent. The successor's Continue endpoint
  (1-p)*B_(i+1)* exceeds its Quit endpoint1+p. The predecessor's
  Continue endpoint is at least1-p>=1-2*p, its Quit endpoint. The mate's
  Continue endpoint is at least4*p+1-p>=1-p, its Quit endpoint. Hence
  this is a nonzero exact Nash root.

For either root, c<1, so(3) gives D'=c*D*<D*. Its prefix lies in K,
contradicting minimality. Thus D*=0. Nonnegative coordinate debts then
give U*=B*. Since (U*,U*) belongs to the ACTUAL semantic carrier,
there are actual independent profiles with both prescribed payoffs and
full caps converging to U*. This proves the claim in Section1, including
all complete deviations and a fixed limiting payoff target.

The argument deliberately avoids the false inference that a
maximal-absorption root selector is lower semicontinuous. Exact-root
spines may approach a cap face where extra nonzero roots appear only at
the limit. Minimization on the entire CLOSED actual carrier chamber
allows that limiting root directly and retains its legal actual-profile
approximation through continuous prefixing.

## 6. Exact checks, source audit, and boundary of the claim

The companion `notes/CODEX_EMMY_BOX__CAP_CHAMBER_SYMBOLIC_CHECK.py`
enumerates all literal coalition endpoints, checks(6)--(8),(10),(12),(13)
symbolically, and checks every seed deadline/Never payoff with exact
rational arithmetic. The inequalities, compact minimization, and consumer
are mathematical proofs above, not inferred from a numerical search.

Named declarations opened before this claim:

* `quittingTerminalSemanticCarrier`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`,
  `quittingTerminalSemanticCarrier_isCompact`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
* `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`;
* `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`
  in `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.

These checked generic declarations support the interpretation of the
ordinary proof; no Lean declaration of the NEW table-specific chamber
invariance or of this raw table's conclusion is asserted. The older
global-minimum cap-Nash argument and its stalling obstruction were checked
narrowly in `notes/CODEX_ROOT__GLOBAL_MINIMUM_HULL_AND_SIGNED_SEAM_BARRIER_REVIEW.md`
and the maintained toolkit. The proposed difference is the invariant
constraint(15), which excludes every positive-debt all-Continue-only cap
face. Cap-Nash debt scaling alone does not do this.

Requested independent falsification: verify EVERY support in Section3,
especially the full-support odds cancellation and the Poisson-binomial
inequality direction; verify that closure and chamber intersection suffice
without a chosen root-spine realization; verify the literal full-cap seed
and the fixed-target unrestricted uniform consumer. Whole existing-producer
coverage of this ONE raw table remains to be checked separately. No
statement for neighboring tables or other K is included in this freeze.
