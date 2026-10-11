# A full-cap chamber for an unbounded asymmetric raw reward family

Status: ordinary complete proof candidate, UNREVIEWED and not Lean-checked.
No export or arbitrary-game theorem is claimed. This is the final coherent
raw-family extension of the fixed-K10 chamber argument. Its important new
point is that the invariant chamber need only be preserved at POSITIVE-debt
points: full-support roots are impossible there. No bound on the magnitude
of the passive triple or grand rewards is assumed.

## 1. Raw data, agency, and conclusion

Players are I=Z/4Z. Live and Never rewards are0. Choose arbitrary finite
real numbers K_i,G_i, for i in I, satisfying ONLY

    K_i>=7,                 G_i<K_i.                    (1)

At the first finite quitting date, let its nonempty quitting coalition S
receive the following ORIGINAL terminal rewards:

    singleton{i}: own1, opposite recipient i+2 gets4, neighbors0;
    adjacent pair{i,i+1}: donor i gets-1, successor i+1 gets2,
                         the two outsiders get1;
    opposite pair: members0, outsiders1;
    triple I\{i}: its members get-1, outsider i gets K_i;
    grand coalition I: recipient i gets G_i.              (2)

Labels are modulo4. Prescribed complete private clocks are independent
laws on Nat union{Never}. Unilateral replacements are ALL unrestricted
complete behavioral strategies, equivalently independent private
date-or-Never laws on the sole live history. There is no public mediator,
correlation between prescribed clocks, or restriction on response clocks.

Claim. For EVERY raw table(1)--(2), there is a fixed vector v and a
sequence of actual independent behavior profiles whose prescribed
terminal payoffs and FULL unilateral caps both tend to v. Consequently
v is a uniform-equilibrium payoff for the original quitting game.
The statement is table-by-table; no uniform rate over this unbounded
parameter set is asserted. Stationary Nash, exact terminal Nash, and an
explicit calendar are not asserted.

In particular the symmetric family K_i=K, G_i=K-1 is covered for EVERY
K>=7, without an upper bound on K. Unequal recipient parameters and
arbitrarily negative grand rewards are allowed by(1).

## 2. Actual full semantics and a compact nonconvex chamber

For an actual profile p, let U_i be its prescribed terminal payoff and
B_i its supremum over ALL unilateral complete replacements. Write

    d_i=B_i-U_i>=0,             D=max_i d_i.

The Never response sees only passive rewards0,1,4,K_i, or Never0. Thus
B_i>=0 even if G_i is negative. For each fixed raw table every U_i and
B_i is bounded by the finite reward bound. Let S be the CLOSED actual
semantic carrier: the closure of ALL actual pairs(U,B). It is compact,
inherits d_i>=0 and B_i>=0, and is invariant under EVERY fixed product
root prefix. No convexity of S or of independent laws is used.

At a product root q in[0,1]^4, define

    c=product_i(1-q_i),   alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(A union{i})],
    b_i=E[r_i(A)*1_(A nonempty)],

where A is the independent opponent quitter set at the root. Exact full
prefix semantics is

    U_i'=q_i Q_i+(1-q_i)(b_i+alpha_i U_i),
    B_i'=max{Q_i,b_i+alpha_i B_i}.                      (3)

For ANY exact mixed Nash root against continuation B, the two-action
finite game identifies the maximum with its on-policy stage payoff:

    B_i'=q_i Q_i+(1-q_i)(b_i+alpha_i B_i),
    d_i'=c d_i,               D'=cD.                  (4)

The finite game always has a mixed Nash equilibrium. Cap attainment is
not required in(3)--(4). These prefix maps are continuous on semantic
pairs, so they preserve S at carrier limits without continuity of a Nash
selector or an approximating sequence of Nash roots.

The literal actual seed is players0,2 Never and, independently, each of
players1,3 Quit0 with probability1/2 and otherwise Never. It gives

    U=(1/4,5/4,1/4,5/4),
    B=(1/2,5/2,1/2,5/2),
    D=5/4,                   sum B-4=2.               (5)

For recipient0 or2 the pure responses Quit0, any positive finite date,
Never pay respectively1/4,1/2,1/4. For recipient1 or3 they pay
1/2,5/2,2. Every complete response law is a mixture of these pure
responses. Thus(5) uses FULL caps and is independent of K_i,G_i: the
seed and its unilateral replacements encounter no PASSIVE triple reward
or grand reward. An outsider's Quit0 response can form a triple, but its
own reward there is the FIXED participant reward-1.

Define the nonempty compact chamber

    C={(U,B) in S: min B<=1, sum B-4 >= (8/5)D}.        (6)

We will prove that EVERY cap-Nash prefix from a POSITIVE-debt point of C
stays in C. We do NOT assert preservation at zero-debt points, where a
diagonal in S already gives the desired conclusion.

## 3. Exact root-support analysis at positive-debt chamber points

### 3.1. No sure root for any continuation

Suppose player i Quits surely in a stage Nash root. Opposite i+2 has
joining-minus-Continue differences-4,-2,G_(i+2)-K_(i+2), according as
zero, one, or two of the other nonowners Quit. All are STRICTLY negative
by(1). Opposite therefore Continues surely. Predecessor i-1 then has
joining differences-1 or-2, so also Continues surely. Successor i+1
strictly joins for2 instead of0. The original sure owner i now gets-1
but can withdraw for0, a contradiction.

Hence every Nash root has q_i<1 for all i. Every active coordinate is
interior and its Quit and Continue endpoints agree. This argument holds
for ANY real continuation B, not only a chamber point.

### 3.2. Full-support roots cannot occur at positive debt

Suppose q has full support and put z_i=q_i/(1-q_i)>0. For recipient i,
write x=z_(i-1), y=z_(i+2), w=z_(i+1), T=xy+xw+yw and V=xyw.
The exact odds numerators of Quit and the opponent-stop term are

    P_i=1+2x-w-T+G_i V,
    N_i=4y+T+K_i V.

Active indifference in(3) therefore gives

    B_i=P_i-N_i=1+2x-w-4y-2T+(G_i-K_i)V.

Let Z=sum_i z_i and E2=sum_(i<j)z_i z_j, and write V_i for the product
of the three opponent odds. Summing gives

    sum_i B_i=4-3Z-4E2+sum_i(G_i-K_i)V_i < 4.          (7)

But a POSITIVE-debt point in C has sum B>=4+(8/5)D>4. Thus NO exact
cap-Nash root there has full support. This is why neither an upper bound
on G_i nor a lower bound on sum_i G_i is needed. In particular we need
not preserve the low-cap condition for all full-support roots at arbitrary
nonnegative B.

### 3.3. Low output cap on every surviving nonzero support

For singleton support owned by i, the output cap B_i'=Q_i is1.

For an adjacent active pair, rotate it to q=(a,b,0,0). Active equalities
and the relevant Quit endpoint are

    B0=(1-2b)/(1-b),      B1=(1+a)/(1-a),
    B0'=Q0=1-2b<1.

B0>=0 implies b<=1/2. For an opposite pair q=(a,0,b,0),

    B0=(1-5b)/(1-b),      B2=(1-5a)/(1-a),
    B0'=Q0=1-b<1,

so a,b<=1/5 and sum_i q_i<=1.

For support three, rotate the missing label to3 and write q=(a,b,e,0),
with a,b,e>0. The relevant active endpoints are

    Q0=1-2b-e+be,       b0=(4-3b)e,
    Q2=1-a+b-2ab,       b2=(4-3b)a.

Active equality and B>=0 imply

    1-2b-5e+4be>=0,
    1-5a+b+ab>=0.

Thus b<=1/2, a<=(1+b)/(5-b)<=1/3, and
e<=(1-2b)/(5-4b)<=(1-2b)/3. Consequently

    sum_i q_i=a+b+e<=2/3+b/3<=5/6<1,
    B0'=Q0<1.                                        (8)

No varied reward appears in these ACTIVE endpoint equalities. An inactive
player's cap inequality may involve its K_i or G_i, but is already
provided by Nash; the proof need not replace or ignore that inequality.

By(7), every cap-Nash root at a positive-debt point of C has support at
most three. The preceding cases prove min B'<=1; all Continue preserves
the input minimum. This is a statement for EVERY root at those points.

## 4. Total-cap ledger without a grand-coalition hypothesis

Let P1 be the root probability of exactly one Quit, P_adj and P_opp the
two types of double Quit, and P_(3,i) the probability that exactly the
triple I\{i} Quits. Since(7) excludes full support, P4=0. The total
finite reward is5 on a singleton,3 on an adjacent pair,2 on an opposite
pair, and K_i-3 on triple I\{i}. Equation(4) gives

    sum B'-4=c(sum B-4)+H,
    H=P1-P_adj-2P_opp+sum_i(K_i-7)P_(3,i).            (9)

For every root with q_j<1 and sum_j q_j<=1, one has P1>=2P2, where
P2=P_adj+P_opp. Indeed, put z_j=q_j/(1-q_j) and Z=sum_j z_j. Cauchy
gives

    sum_j q_j=sum_j z_j/(1+z_j)
                 >= Z^2/(Z+sum_j z_j^2).

For Z>0 the premise sum_j q_j<=1 implies
2E2=Z^2-sum_j z_j^2<=Z. Multiplication by c yields2P2<=P1.
The zero root is immediate.

For opposite and three-support roots, the bounds of Section3 give this
premise. Hence(1) implies

    H=(P1-2P2)+P_adj+sum_i(K_i-7)P_(3,i)>=0.

For an adjacent pair, H=a+b-3ab>=0 because b<=1/2: if b<=1/3 this
is immediate, and otherwise the minimum over0<=a<=1 is1-2b>=0.
For a singleton H=q_i>=0, and for all Continue H=0.

Thus EVERY cap-Nash root at a positive-debt point of C satisfies

    min B'<=1,       sum B'-4>=c(sum B-4),       D'=cD.

Together these inequalities prove that its actual semantic prefix again
belongs to C. No total-grand-reward assumption has been introduced.

## 5. Global minimization and the actual full-behavior consumer

Let (U*,B*) attain the minimum D* of D on C. If D*=0, its nonnegative
coordinate debts imply U*=B*, a diagonal in S.

Otherwise sum B*>4 and min B*<=1. A nonzero cap-Nash root exists:

* If min B*<1, all Continue is not Nash. Finite mixed Nash existence
  therefore supplies a nonzero root.
* If min B*=1, all caps are>=1 and some exceed1. There is a cycle edge
  i to i+1 with B_i*=1 and B_(i+1)*>1. Let only i Quit, with

      0<p<min{1,(B_(i+1)*-1)/(B_(i+1)*+1)}.

  Owner i is indifferent. Successor's Continue endpoint is
  (1-p)B_(i+1)*>1+p, its Quit endpoint. Predecessor's Continue is at
  least1-p>=1-2p, its Quit endpoint. Mate's Continue is at least
  4p+1-p>=1-p, its Quit endpoint. This is a nonzero exact Nash root.

For either root, q_j<1 and c<1. Sections3--4 put its prefix back in C,
where(4) gives D'=cD*<D*, contradicting minimality. Hence D*=0.

Diagonal membership in the CLOSED ACTUAL carrier supplies a sequence
of actual independent prescribed profiles with both U and full B tending
to the SAME fixed target v. Their maximum complete terminal regret tends
to0. The checked terminal-to-uniform consumer gives a uniform-equilibrium
payoff for the original raw table. Every unilateral complete behavioral
replacement, including Never, is retained throughout.

This optimizes over the ENTIRE compact chamber, not one exact-root spine
or a fixed initial profile. A Nash root appearing only at the minimizing
limit is legal: the fixed product-prefix map is continuous and preserves
the closed actual carrier. No Nash-selector continuity is asserted.

## 6. Exact source interpretation and requested falsification

The generic semantic facts used above are:
`quittingTerminalSemanticCarrier`,
`quittingTerminalSemanticCarrier_isCompact`,
`exists_terminalProfile_sequence_tendsto_semanticPair`, and
`quittingTerminalSemanticPrefix_mem_carrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`;
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
`UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`; and
`isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier` in
`UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.
These declarations support the generic interpretation; no checked Lean
declaration of the NEW raw-family chamber argument is asserted.

Requested independent falsification: check the exact parameter-free
support-three endpoints, the full-support sum(7), restriction to
POSITIVE-debt chamber preservation, arbitrary negative G_i, all complete
seed caps, and the source-to-fixed-target consumer. Whole existing raw
producer coverage of this family remains a separate review question.
No larger family or arbitrary-game reduction is inferred from this one.
