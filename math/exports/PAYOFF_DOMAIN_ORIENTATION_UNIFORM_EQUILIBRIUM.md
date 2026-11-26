# Uniform equilibrium from payoff-domain orientation

This ordinary mathematical theorem gives a raw reward criterion for any
finite nonempty player set. It uses joint payoff geometry at zero-debt
limits, while retaining every full unilateral deviation cap. Weak local
orientation is tested only near relevant payoff domains; every sure root
is a good exit. Two complete raw adapters are proved: the reward hull and
a smaller first-action outer set. An explicit Fin4 table escapes the earlier
raw admissions audited below. No new Lean check or arbitrary Fin4 solution
is asserted.

## 1. Exact raw theorem

Let I be finite nonempty, n=|I|>=1. At each live date owners independently
choose Continue or Quit. The first nonempty quitter coalition S absorbs
at finite reward r(S); live play and Never give zero. One owner may
replace its complete behavioral law. Assume s_i=r_i({i})>=0 and put
Z_i(S)=r_i(S)-s_i on nonempty S, so native own singletons vanish.

For product hazards q in[0,1]^I define H_i=product_(j!=i)(1-q_j),
h=product_i(1-q_i), and let A be the independent opponent quitter set:
Q_i(q)=E[Z_i(A+i)], P_i(q)=E[Z_i(A)1_(A nonempty)].
These are literal finite reward polynomials. Define
H=conv({0} union {Z(S):S nonempty}) and m_i=min(0,min_S Z_i(S)).
The canonical first-action outer set is

    N1={u in H: there exists q in[0,1]^I such that for every i,
           Q_i(q)<=u_i,
           q_i(u_i-Q_i(q))=0,
           P_i(q)+m_i H_i(q)<=u_i}.                  (N)

Choose either of these two raw source domains Omega:

* Hull domain: Omega=H+[-epsilon,epsilon]^I, epsilon>=0, with nonempty
  interior. If epsilon>0 this is automatic; if epsilon=0 it is the
  finite full-rank condition that the reward vectors span R^I.
* First-action domain: Omega=N1+(-epsilon,epsilon)^I for some epsilon>0.
  No prefix invariance or interior condition on N1 is assumed.

Put Omega_minus={v in Omega:min_i v_i<0}. For every support S with2<=|S|<=n,
positive odds z in R^S, and z_T=product_(j in T)z_j, set

    Phi_i^S=sum_(empty!=T subset S-i) z_T[Z_i(T+i)-Z_i(T)],
    R_i^S=sum_(T subset S-i) z_T Z_i(T+i), i in S.

Require the weak orientation test

    all active R_i^S>0 and Phi^S in projection_S(Omega_minus)
            => (-1)^|S| det D Phi^S<=0.             (W)

All premises are finite real-polynomial tests on the reward table and
numerical epsilon. Hull membership is a nonnegative convex-weight solve;
N1 membership is exactly(N), not an assumed Nash profile. Domain and
projection membership introduce only finitely many real variables and
strict or weak polynomial inequalities.

**Theorem.** The native infimum A_Z of total full unilateral regret over
actual absorbing profiles is zero. Every nonnegative recipient-row raise
of Z, including r, therefore has one uniform-equilibrium payoff target,
fixed before accuracy, against all complete behavioral replacements.
No root selector, actual continuation, cap carrier, derivative at a
selected strategy, or strategic index budget is supplied.

## 2. Exact prefixes and a common local assertion

For an actual native profile write U_i for prescribed terminal payoff,
B_i for the supremum over ALL unilateral behavioral replacements, and nu
for joint Never. Put d_i=B_i-U_i>=0 and D=sum_i d_i. For a product prefix q,

    h=product_i(1-q_i), H_i=product_(j!=i)(1-q_j),
    Q_i=E[Z_i(A+i)], P_i=E[Z_i(A)1_(A nonempty)],
    E_i=q_i Q_i+(1-q_i)P_i,

where A is the independently sampled opponent quitter set. The exact updates
are

    U'_i=E_i+h U_i,
    B'_i=max(Q_i,P_i+H_i B_i), nu'=h nu.              (1)

There is one live public history, repeated all Continue. Every complete
behavioral replacement disintegrates into pure deadlines and Never; (1)
therefore prices all deviations. It also defines virtual data initialized
at U=B=v,nu=1. No actual-cap realization of this initialization is asserted.
The identity

    d'_i=q_i(B'_i-Q_i)+(1-q_i)(B'_i-P_i-H_i B_i)
                               +(1-q_i)H_i d_i>=0    (2)

preserves nonnegative debt for arbitrary product prefixes. Both U and B
are coordinatewise1-Lipschitz in their initial annotations, uniformly over
all finite word lengths. All coordinates stay bounded by a common M>=1 bounding the rewards and
initial annotations in each fixed local argument. The actual global data
are bounded by the reward bound. An arbitrary open domain need not be bounded.

For an annotation v define F_q(v)=E+h v. A Nash root uses only maximizing
actions between Q_i and P_i+H_i v_i. Prefixing it to U=B=v preserves U=B.
Call it good if some q_i=1 OR min_i F_q(v)_i<=0. Nash and good-root graphs
are closed; finite mixed Nash existence gives a nonempty Nash graph.

There are two source-domain consumers.

(i) K is compact, contains0 and satisfies F_q(K) subset K for EVERY
product q; every v in K with min v<=0 has a good Nash root.

(ii) O is open and contains every payoff projection U of the actual-data
closure with B=U,nu>0,min U<=0; every v in O with min v<=0 has a good
Nash root. These are zero-debt CLOSURE points, not just payoffs of actual
exact equilibria. No invariance of O or a smaller outer set is required.

Either condition implies A_Z=0. To prepare (i), every actual U lies in K:
truncate its stopping laws after N dates to Never. The truncated payoff
comes from finite prefixes of0, and converges to U. Closedness gives
membership also in the actual-data closure. Virtual U initialized in K
also stays in K. Under (ii), virtual payoffs may leave O; the local proof
queries a selector only while a displacement bound keeps the input in O.
Arbitrary positive-debt caps B need not lie in either domain.

We first prove a local assertion at v in the relevant source domain,
v>=0,min v=0, when AllContinue
is its only good root. Let S={i:v_i=0}. Given any hazard bound and eta in
(0,1), there are finite words of S-supported PRODUCT prefixes, each below
that bound, with survival in[1-eta,1-c] for a fixed c>0, whose debt from
U=B=v tends to zero and whose payoff minimum has limsup<=0. The words
need not be exact Nash. The proof is induction on |S|.

Write Gamma_ij=Z_i({j}). If Gamma_SS has a nonzero nonnegative kernel
vector x, normalize sum x=1. Repeat q=delta*x for floor(T/delta) prefixes,
with fixed sufficiently small T>0 and delta tending to zero. For core
owners, P_i=O(delta^2),Q_i=O(delta),E_i=O(delta^2). Equation(1) bounds
core payoffs and cap errors by O(delta) over the whole word. Positive
outsiders retain Continue buffers for small T, so their cap and payoff
updates coincide. Survival tends to exp(-T) in(1-eta,1). This proves the
assertion, including singleton S. These are approximate, not exact, roots.

Otherwise zero is outside the convex hull of the columns of Gamma_SS.
Strict separation gives a signed row w with every coordinate of w Gamma_SS
strictly positive. For all sufficiently small S-supported product q,

    w E_S(q)>=gamma*sum_i q_i>=0                    (3)

for a fixed gamma>0. Choose delta>0 below the requested hazard bound, the
bound for(3), and eta/(4n). Closedness of the good-root graph implies that
all good roots at nearby domain points with min<=0 are arbitrarily small;
otherwise a convergent subsequence gives a nonzero good root at v.
At small roots every positive outsider strictly Continues. Thus choose
rho>0 so every good root at such an input within rho of v is S-supported
with hazards below delta, and every formerly positive coordinate stays
positive. In case(ii) also make the rho-ball around v lie inside O.
Before choosing a seed, fix

    c0=min(eta/4,rho/(8M),1/4)>0.

Choose j in S and small t>0. The exact solo prefix gives
z=(1-t)v+t Gamma[:,j], z_j=0, ||z-v||<rho/4, and
w z_S=t w Gamma_Sj>0. Initialize virtual U=B=z,nu=1; these are not the
actual caps of that solo prefix. In case(i), prefix invariance puts z
in K; in case(ii), its small displacement puts z in O.
Take the compact closure of outputs of ALL finite S-supported product
words with hazards at most delta and survival h>=1-eta. Minimize h on
its closed subset

    B=U, min U<=0, w U_S>=h w z_S.                   (4)

The empty word is feasible. In case(i) every such U belongs to K.
Every word has
||U-v||<=||z-v||+2M(1-h). If a minimum has h>1-c0, its U is within rho/2
of v, hence in O in case(ii). A nonzero good Nash root there is small
and S-supported; it preserves
zero debt, the nonpositive minimum and(4), by(3). Its resulting survival
is greater than(1-n*delta)(1-c0)>1-eta but smaller than h, a contradiction.
Hence only good AllContinue remains, forcing U>=0. Its zero set T is
nonempty and a proper subset of S, because w U_S>=h w z_S>0.

This U belongs to the relevant source domain in either case.
Apply induction at U with hazard bound delta and a survival budget eta1
small enough that h(1-eta1)>1-eta. Its arbitrary T-supported product words
also preserve the ORIGINAL w inequality through(3). A compact endpoint
has zero debt, nonpositive minimum and strictly smaller survival, still
in the same minimizing set. Approximate the minimizing point by its
seed-generated words and then append each finite extension; continuity
(indeed the uniform1-Lipschitz bound) and strict survival slack place this
endpoint in the original closure. This contradicts minimality.
Every seed minimum therefore has h<=1-c0; in case(ii), its location
outside O would be harmless because no further selector is queried.
Let t tend to zero and apply
its approximating words to v instead of z. The uniform Lipschitz bound
gives debt tending to zero and limsup min U<=0, with survival eventually
at most1-c0/2. This completes the local induction. All original survival
factors are retained; there is no conditional-tail reset.

## 3. Actual minimum, repair, and the raw domain adapters

Now consider the compact closure C of ALL actual data(U,B,nu). Every
product prefix acts continuously and preserves C. For an actual profile,
move a smallest marginal Never mass, at most nu^(1/n), to a finite date.
The profile becomes absorbing. All n prescribed payoffs and the n-1 other
full caps change by at most2M times that mass; its owner's cap is unchanged.
Therefore, also by continuity on C,

    A_Z<=D+(4n-2)M nu^(1/n).                         (5)

Minimize nu on B=U,min U<=0 in C. AllNever makes this set nonempty:
native payoffs and all full caps are zero. If A_Z>0, (5) gives a positive
minimum m. At its minimizer U=B=v lies in the source domain: by
invariance and truncation in(i), and by the closure hypothesis in(ii).
A sure good root would give
zero debt and nu=0, contradicting(5); a nonzero proper good root would
retain min U<=0 and lower nu, contradicting minimality. Thus only good
AllContinue remains, so v>=0,min v=0. The local assertion, applied via
continuous finite prefixes of C, gives a zero-debt endpoint with min U<=0
and original Never at most m(1-c)<m. This contradiction proves A_Z=0.

For the hull adapter, F_q(H+closed epsilon cube) stays in the same set:
F_q(w) is a convex combination of w and reward vectors, and an error e
becomes h e. Thus consumer(i) applies once(W) supplies its selector.

For the first-action adapter, N1 is compact by its closed definition
inside H times the compact hazard cube. Let q be the first-date hazards
of ANY actual profile and d_i=B_i-U_i. The following exact inequalities
hold for every profile, without equilibrium assumptions:

    Q_i(q)-U_i<=d_i,
    q_i(U_i-Q_i(q))<=(1-q_i)d_i,
    P_i(q)+m_i H_i(q)-U_i<=d_i.                       (6)

The first follows from B_i>=Q_i. The prescribed Continue payoff is also
at most B_i, so U_i<=q_i Q_i+(1-q_i)B_i proves the second. The third follows from
B_i>=P_i+H_i Btail_i and Btail_i>=m_i. These bounds include every behavioral
deviation and off-path continuation. At any zero-debt actual-closure point,
choose a convergent subsequence of these first-date hazards. Then(6)
gives(N), including equality in the middle condition because Q_i<=U_i.
Every U lies in H, so EVERY zero-debt actual-closure payoff lies in N1.
Its open epsilon-neighborhood therefore supplies consumer(ii)'s entire
source-containment hypothesis. No positive-debt cap is substituted for U.

The remaining common input, the selected good root, is produced by(W).
The map T_i(q)=clip_[0,1](q_i+Q_i-P_i-H_i v_i) has exactly the Nash
roots as fixed points. Use the polynomial formulas Q,P,H also outside
the cube. Its homotopy to the constant half-vector has no fixed point on
the boundary of(-1,2)^I, so its total fixed-point index is+1.
For proper hazards Q_i-(P_i+H_i v_i)=H_i(Phi_i-v_i). Choose a generic
v in the interior of the selected domain Omega with min v<0, avoiding
every active-map critical value and every inactive-tie image. These sets are null:
polynomial equal-dimensional critical images have one O(h^2) width and
others O(h) on bounded cubes; covering by O(h^-m) cubes gives volume O(h).
An inactive-tie image has n-1 source variables mapping into n coordinates
and is null by Lipschitz cube covers. Finite supports and countable exhaustion
give density. Every proper root is regular with strict inactive comparisons.

Suppose no good root exists. Every root is proper, every successor is
strictly positive, and every active R_i>0. AllContinue is excluded by the
strict source deficit; a singleton active root has output0, so is excluded.
On support S the active annotation is Phi^S=v_S in projection_S(Omega_minus).
By(W) its signed determinant is nonpositive, and regularity makes it
strictly negative. Thus every root has full ambient index-1: proper
inactive coordinates contribute identity blocks, and the active index is
(-1)^|S| sign det D Phi^S. The active gap derivative differs from D Phi^S
only by positive row survival factors and positive odds-coordinate factors;
inactive displacement rows give identity blocks. The compact root set is finite, so its total
index is negative, contradicting+1 for the clipped Nash self-map of the
cube. No reward perturbation is needed for weak or rank-deficient strata:
generic sources simply avoid their critical images. Sure roots were good
from the outset, so no one-sure sign test is necessary.

For a nongeneric v in Omega with min v<0, approximate by generic sources
inside Omega. This is immediate in the open case. In the closed hull case,
mix slightly toward any interior point of Omega and then perturb, keeping
the negative coordinate. Compact roots and the closed good-root graph
give a good root at v. If min v=0, v>=0 and AllContinue itself is good.
This supplies every selected-root condition used by the two consumers.

An absorbing prescribed profile gains the full row raise s_i>=0, while any
deviator gains at most s_i. Its original regret is therefore at most its
native regret. Terminal approximate Nash profiles at every accuracy select
one fixed uniform target by
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The exact full-cap update corresponds to
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
The source-domain consumers and these raw adapters are ordinary
mathematics not newly checked in Lean. No strategic input remains assumed.

## 4. A universal actual-source accumulation restriction

For any native table with A_Z>0, choose the actual-closure minimum m of nu
over B=U,min U<=0 used above. Its minimizing data satisfy U=B=v in N1,
nu=m>0. Every nonzero good Nash root at v would lower original Never or
absorb with zero debt. Therefore there are exactly two possibilities.

If min v<0, AllContinue is not Nash and NO good root exists: every root
at v is proper with strictly positive successors. Closedness of the
good-root graph and compactness of hazards make this failure persist on
an open neighborhood, including generic strict negative inputs.

If min v=0, then v>=0 and AllContinue is the only good root. For EVERY
delta>0 some u with ||u-v||_infinity<delta,min u<0 has no good root.
Otherwise all strict negative inputs in the open delta-ball have good
roots, and at min=0 AllContinue is already good. The local assertion for
that open domain then lowers m, a contradiction.

Thus bad strict-negative sources accumulate at an actual zero-debt
CLOSURE payoff/cap pair U=B=v in N1 with min v<=0. In the negative case
v is itself a bad source; in the boundary case the bad sources approach
it. No actual profile attaining this closure point is asserted. The
positive least-Never value m is essential: arbitrary actual boundary
membership is not a conjecture obstruction. This is a necessary condition
for A_Z>0, not a converse or a counterexample inferred from a failed test.

## 5. A complete continuous Fin4 family: all C>=6/7

Let C>=6/7 and use the following complete native table, with mask bit i
meaning owner i quits. Original rewards may be any nonnegative own-row
raise of this table, in particular r=Z+1.

| Mask | Z0 | Z1 | Z2 | Z3 |
| --- | ---: | ---: | ---: | ---: |
| 1 | 0 | -1 | 3 | -1 |
| 2 | -1 | 0 | -1 | 3 |
| 4 | 3 | -1 | 0 | -1 |
| 8 | -1 | 3 | -1 | 0 |
| 3 | -2 | 0 | 0 | -9/10 |
| 5 | 1 | 1/2 | 1 | 1/2 |
| 9 | 1/10 | -9/10 | 0 | -4 |
| 6 | 0 | -4 | 0 | -9/10 |
| 10 | -10 | -1 | -10 | -1 |
| 12 | 0 | -9/10 | -2 | 0 |
| 7 | -10 | 1 | -10 | -1-C |
| 11 | -10 | -1 | -10 | -1 |
| 13 | -10 | -1-C | -10 | 1 |
| 14 | -10 | -1 | -10 | -1 |
| 15 | -11 | -1 | -11 | -1 |

Take epsilon=0, so K=H. The four singleton columns form the invertible
matrix Gamma=[0,-1,3,-1;-1,0,-1,3;3,-1,0,-1;-1,3,-1,0],det Gamma=45.
The positive relation

    7Z(1)+5Z(2)+7Z(4)+5Z(8)+Z(15)=0

has coefficient sum25. These five vectors form an affine simplex of full
dimension, so0 is interior H for every C.
Pair02 is the only pair with both participant premiums positive, and its
joining gaps are(-2,-2), giving determinant-4. On013,123 owner3 has all
participant premiums nonpositive, so their high-premium domains are empty.

With D=2+10(y+t)+yt, the full joining maps are

    Phi0=-y+11t/10-Dz, Phi2=y-t-Dx,
    f=Phi1=x-3z+xz/2-4t-t(x+z)/10+C*xzt,
    g=Phi3=-3x+z+xz/2-4y-y(x+z)/10+C*xyz.

On012, high R1=z(x-4)>0 gives x>4. At fixed anchor levels,
D f_y=4-(21/2)x+(61/2-10x)z<0. The transverse anchor determinant is
-D^2, so the triple's signed index determinant is strictly negative.
On023, high R3=x(z-4)>0 gives z>4, and
D g_t=41/10-(21/2)z+(611/20-10z)x<0. Both triple orientation tests
therefore hold on their entire positive-premium domains, independently
of the hull and of C.

For full support, R1=z(x-4)-t(1+x+z+xz)>0 and
R3=x(z-4)-y(1+x+z+xz)>0 force x,z>4. Set

    L(w)=(14/3)(w1+w3)-w0-w2.

Every native reward and Never has L<=16. The two exceptional triples
have L=20-(14/3)C<=16; singleton masks2,8 have L=16; grand has L=38/3;
all remaining entries are smaller. Thus every v in H has L(v)<=16.
But for full positive premiums,

    L(Phi)=(14/3)xz-(22/3)(x+z)
      +(y+t)[(143/15)(x+z)+(14C/3)xz-56/3]
      +yt(x+z)-t/10 >16.

The first line equals16 at x=z=4 and strictly increases in either
anchor. The bracket, even after subtracting1/10 to absorb the last
term, is positive for x,z>=4,C>=6/7. Hence no full high annotation lies
in H, and its(W) test is vacuous. Every support test is now proved.
The theorem supplies A_Z=0 and UE for this whole C>=6/7 family.

The threshold6/7 is the boundary of this particular linear separator:
at C=6/7 the limiting full-high annotation(-8,0,-8,0) belongs to H as
(2/9) times the average of singleton masks2,8 plus(7/9) times the average
of triple masks7,13. It is not a positive-odds full root; every actual
high full root still satisfies the strict inequality above. No claim of
failure below6/7, or of arbitrary Fin4 closure, follows from this boundary.

## 6. Strict new coverage at C=6

This section concerns the literal table in Section5 at C=6, with original
rewards Z+1. Its source-to-UE conclusion follows from the hull adapter,
without using a tilted rectangle or a supplied strategy.

### Every direct cooperative-edge selection fails

The earlier direct rectangle entrance used the sole positive pair02 as
anchors, positive sides L1,L3 and capture depths kappa0,kappa2, and required
the two reduced cross derivatives f_t>=0 on the right edge and g_y>=0 on
the top edge at ALL deeper anchor source levels. The following argument
excludes every possible parameter choice, not one selected certificate.

Any admissible capture constants must have kappa0,kappa2<=8: let high
axis odds tend to x=4,y=0 on012 and z=4,t=0 on023. Their deep source
coordinates tend to-8. Write arbitrary candidate sides y=L1>0,t=L3>0,
and put s=y+t,p=yt. With f,g the raw maps at C=6, define
Cedge=D*f_t+[-1-(10+y)x]*f_x+[11/10-(10+y)z]*f_z and
Gedge=D*g_y+[1-(10+t)x]*g_x+[-1-(10+t)z]*g_z.
These are D times the two reduced cross derivatives.
Their leading xz coefficients are

    (Cedge)xz=2+59y-60t-6yt, (Gedge)xz=2+59t-60y-6yt.

Both must be nonnegative at the shared upper corner, by letting both
anchors tend to infinity. Their sum gives4-s-12p>=0, hence s<=4.
Fix a=-8 and let c tend to minus infinity. The anchor
z=(8-y+11t/10)/D is positive by the earlier positive-anchor rectangle
premise, and the coefficient of x in Cedge must be

    A=(80ty²+2265ty-11222t-1580y²+7390y-66)/(20D)>=0.

Symmetrically, at c=-8,x=(8+y-t)/D the coefficient of z in Gedge must be

    B=(40t²y-790t²+1013ty+3690t-5630y-34)/(10D)>=0.

But

    20D(A+B)=80ps-1580s²+7451p-3856s+14(t-y)-134
      <=20s³+(1131/4)s²-3842s-134
      <=-2391s-134<0,

using p<=s²/4,|t-y|<=s and0<s<=4. This contradiction excludes EVERY
choice of sides and capture constants in the earlier un-tilted criterion.
Positive recipient scales normalize out of the anchor bounds and derivative
signs. Pair02 is the only possible anchor pair; exchanging its owners or
the free owners just exchanges these arguments. Thus all label and scale
choices of that earlier complete raw producer fail.

### Every stationary and earlier raw selection in the comparison

A stationary profile repeats one independent hazard vector forever.
All Never fails because own immediate Quit earns one. A sole active owner
is defeated by its successor on0->1->2->3->0: the successor's native
passive reward is-1, its participant premium is nonnegative, and its
joining gain is respectively(1,1,1,11/10).

There is no Nash root with a sure owner, whatever its continuation. Sure0
forces2 quiet by conditional joining gaps(-2,-10,-10,-1), then3 quiet
by gaps(-3,-1/10), then1 sure by gap1; owner0 now has gap-1 and withdraws.
Sure2 is symmetric. If1 alone is sure, owner0 has gap numerator
-1-10z-zt<0 and becomes quiet; owner3 then has numerator-4-z/10<0 and
becomes quiet; owner2 must be sure, already excluded. Sure3 is symmetric.
If both1,3 are sure, the anchor gaps are exactly-q2,-q0, so both anchors
cannot be active. If q0=0, owner3's gap is-4(1-q2)-q2/10<0; otherwise
q2=0 and owner1's gap is-4(1-q0)-q0/10<0. All cases contradict Nash.
These cascades also exclude every persistent-base/free-set/induced-root
choice with any punishment tail, rather than just stationary repetition.

A proper stationary pair ij requires q_j Z_i(ij)=Gamma_ij, where
Gamma_ij=Z_i(j). Pairs01,12,23 have a zero participant entry against a
nonzero singleton; pairs03,13 require a negative ratio;02 requires ratio3.
For proper support S, put D_i=product_(j in S-i)(1+z_j) and
P_i=sum_(empty!=T subset S-i)z_T Z_i(T). Stationarity requires

    E_i=(D_i-1)R_i-D_i P_i=0.                          (3)

On012 in order(0,1,2), and023 in order(2,3,0), with odds(x,y,z),

    E0=y(1-y)-3z-10y²z²-11y²z-12yz²-3yz-2z².

Its zero forces0<y<1,z<y(1-y)/3<=1/12. But
2E1=(z²+3z+2)x²+(2-5z-5z²)x+2z-6z²>0 there; its linear coefficient
after division by2 is at least223/288. Neither triple is stationary.
On013 in order(0,1,3),
10E0=-10y²(z+1)+y(11z²+101z+10)+11z²+10z>0 for0<y<=1.
On123 in order(2,3,1),
E0=-y²(z+1)+y(z²+10z+1)+z²+z>0 for0<y<=1.
Hence both require y>1, whereas their common last-owner residual is
10E2=-x²y²-31x²y-30x²-41xy²-61xy+10x-40y²-30y<0 then.

For full proper support the20 multiplier terms

    W0=2+t+zt+2y+8x+8xt+3xy+10x²,
    W1=3+8y+y², W2=2+2t+8z+10z²+y+9yz+2xy, W3=2+8t

give -10 sum_i W_i E_i with141 nonzero coefficients, all positive,
sum95667, maximum3920. This excludes their common zero. The following
standalone standard-library calculation verifies EVERY coefficient exactly, without root searches or floating-point steps.

```python
from fractions import Fraction as F
Z={1:[0,-1,3,-1],2:[-1,0,-1,3],4:[3,-1,0,-1],8:[-1,3,-1,0],
   3:[-2,0,0,F(-9,10)],5:[1,F(1,2),1,F(1,2)],
   9:[F(1,10),F(-9,10),0,-4],6:[0,-4,0,F(-9,10)],
   10:[-10,-1,-10,-1],12:[0,F(-9,10),-2,0],
   7:[-10,1,-10,-7],11:[-10,-1,-10,-1],
   13:[-10,-7,-10,1],14:[-10,-1,-10,-1],15:[-11,-1,-11,-1]}

zero=(0,0,0,0)
W=[{zero:2,(0,0,0,1):1,(0,0,1,1):1,(0,1,0,0):2,
    (1,0,0,0):8,(1,0,0,1):8,(1,1,0,0):3,(2,0,0,0):10},
   {zero:3,(0,1,0,0):8,(0,2,0,0):1},
   {zero:2,(0,0,0,1):2,(0,0,1,0):8,(0,0,2,0):10,
    (0,1,0,0):1,(0,1,1,0):9,(1,1,0,0):2},
   {zero:2,(0,0,0,1):8}]
def add(p,q,scale=1):
    r=p.copy()
    for a,c in q.items(): r[a]=r.get(a,F(0))+scale*c
    return {a:c for a,c in r.items() if c}
def mul(p,q):
    r={}
    for a,c in p.items():
        for b,d in q.items():
            e=tuple(a[j]+b[j] for j in range(4))
            r[e]=r.get(e,F(0))+c*d
    return {a:c for a,c in r.items() if c}
certificate={}
for i in range(4):
    D,R,P={},{},{}
    for mask in range(16):
        if mask&(1<<i): continue
        a=tuple((mask>>j)&1 for j in range(4))
        D[a]=F(1); R[a]=F(Z[mask|(1<<i)][i])
        P[a]=F(Z[mask][i]) if mask else F(0)
    E=add(mul(add(D,{zero:F(1)},-1),R),mul(D,P),-1)
    certificate=add(certificate,mul(W[i],E),-10)
assert len(certificate)==141 and all(c>0 for c in certificate.values())
assert sum(certificate.values())==95667 and max(certificate.values())==3920
print('PASS: 141 strictly positive stationary-certificate coefficients')
```

Stationary approximation also fails. The singleton matrix and inverse are

    Gamma=[0,-1,3,-1;-1,0,-1,3;3,-1,0,-1;-1,3,-1,0],
    Gamma^-1=[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2]/15>0.

It is R0: a nonzero x>=0,Gamma*x>=0,x_i(Gamma*x)_i=0 cannot have
singleton support because every column has a negative exterior entry.
Larger supports are impossible since every principal block is invertible:
pair determinants-1 or-9, triple determinants6, full determinant45.
If stationary debt tended to zero with a nonzero limiting hazard, it would
give an already excluded stationary Nash profile. If hazards tend to zero,
normalize their sum to p. Singleton absorption gives limiting payoff
1+Gamma*p. Immediate Quit forces Gamma*p>=0; for p_i<1, Never gives
1+(Gamma*p)_i/(1-p_i), forcing p_i(Gamma*p)_i<=0. For p_i=1 that product
is zero directly. R0 contradicts both cases. Thus all stationary profiles
have a strictly positive debt gap, also excluding their reward closure.

At odds(41/10,1/1000,41/10,1/1000),

    R=(40160449/10^7,38399/100000,40159449/10^7,38399/100000)>0,
    eta=Phi=(-82819041/10^7,3763/12500,-82820041/10^7,3763/12500),
    det D Phi=1037746771396196253/312500000000000>0.

At original annotation1+eta all active owners are indifferent and above
their singleton. Full-support Low and individual negative Orientation
therefore fail, even after any positive recipient scaling. Charge fails
since its required nonpositive pair coefficient is instead
P_I(02)=lambda1 Z1(012)+lambda3 Z3(023)=lambda1+lambda3>0.
Every earlier independent Low/Charge/Orientation support assignment fails,
including assignments with distinct pair--triple repairs on proper supports.

The four crossing-pair native vectors sum to(-19/10,-29/5,-2,-29/5).
Thus no nonzero nonnegative weight has nonnegative whole-payoff ledger on
every proper coalition; finite families and positive matrix changes do
not help. For support-filtered ledgers w*Gamma>=0 and Gamma^-1>0 force
w>0, reducing to the same contradiction. The three inserted-premium
singleton1,2,3 inequalities sum to
-(9/10)w0-5w1-2w2-w3>=0, again impossible. Scales absorb into the weights.
For ordered marked blocks, a mark in02 makes the first block meeting02
have a positive participant sum. Otherwise a marked1 fails on012 or a
marked3 on023. This exhausts all sets, orders and positive block weights,
and makes the greatest premium core all four owners. Every row also has
a negative participant, excluding globally protected owners; no row has
all participant premiums nonpositive, excluding all passive-bound,
opposed-path and quiet-face role choices.

All principal triple inverses have negative diagonals(two-1/6,one-3/2),
so no nonnegative-inverse triple extension applies. Reciprocal singleton
signs agree, excluding opposite-sign requirements. The full R0 degree is
one: at LCP target1 only full support is feasible, with solution(1,1,1,1)
and determinant45. Singletons fail; negative pairs give negative solutions;
favorite pairs violate exterior residuals; triple solutions are negative,
with entries(-1/2,-5/2,-1/2). These matrix exits do not decide the table.
The three matching joining-sign lists are
01|23:(-,+),(-,+);02|13:(-,-),(-,-);03|12:(+,-),(-,+).
No matching has four nonnegative gaps or four positive participant premiums.
Signed positive inverse columns force all signs positive and cannot repair
this. Favorite joining gaps are negative; common favorite premiums cannot
have endpoints(1,1,-1,-1) after the singleton-normalized equal row scales.
Positive Z0(03)=1/10 defeats all-cross-nonpositive templates; a nonnegative
endpoint in every crossing pair defeats all-cross-strictly-below templates.
Positive favorite02 defeats all-favorite-nonpositive templates. No triple
has six positive joining gaps. These tests exhaust the respective pair,
favorite-schedule and positive-joining collision-box selections.

The broader three-owner joint-return entrance requires, in its roles,
Gamma03>0,Gamma23<0,Z2(23)>0. The sole positive crossing participant
forces roles(0,1,2,3)=(actual1,actual2,actual0,actual3). Define e=Gamma32,
d=-Gamma30,w=Z3(02),v=Z3(23),a3=Z3(03),t3=Z3(023). These give
e=-1,d=-3,w=-9/10,v=-4,a3=t3=-1,omega=w+d-e=-29/10.
Thus J0=e*a3+d*v=13,J1=e*(t3-a3)-(omega+e)*v=-78/5. The unique root
b=-J0/J1=5/6 gives next hazard e*b/(d-omega*b)=10/7>1.
All positive recipient scales cancel from these ratios.

The signed solo/triple entrance instead solves
[Z_r(rk),Z_r(rj);Gamma_rk,Gamma_rj](u,v)=(-Z_r(rjk),-Z_r(jk))
and requires u,v>0. Swapping j,k swaps u,v; these12 rows cover all24 roles:

| r;j,k | u,v |
| --- | --- |
| 0;1,2 | -2,-6 |
| 0;1,3 | -100/21,-110/21 |
| 0;2,3 | 300/13,100/13 |
| 1;0,2 | 1/4,1/4 |
| 1;0,3 | -1,-39/10 |
| 1;2,3 | 1/5,-3/10 |
| 2;0,1 | 30,10 |
| 2;0,3 | -6,-2 |
| 2;1,3 | -5,-5 |
| 3;0,1 | 1/5,-3/10 |
| 3;0,2 | 1/4,1/4 |
| 3;1,2 | -39/10,-1 |

For clarity, the second-phase hazards are q_j=1/(1+u),q_k=1/(1+v),
q_r=b,q_o=0. For i=j,k put d_j=1-q_k,d_k=1-q_j,G_i=Gamma_ir and form
its literal forced-Quit and passive averages Q_i(b),P_i(b). Set
psi_i=Q_i-P_i-d_i(1-b)Q_i,L_i=d_i(1-b)(G_i-Q_i).
Active indifference requires psi_i=s L_i for the solo hazard s. Eliminating
s gives psi_k L_j-psi_j L_k=0; s=psi_i/L_i when L_i!=0.
After removing the nonzero factor1-b, the four surviving rows require
820022b²-2046081b+391876=0; b(3b-4)=0;
7088b²-19809b+3844=0; b(3b-4)=0.
Owners1,3 have no root in(0,1). The other quadratics decrease on[0,1],
are positive at1/5 and negative at1, hence their only candidate has b>1/5.
Its produced solo hazards are respectively
(400b²+38021b-1131)/[100(b-1)(4b+365)] and
(20b²-359b+9)/[10(b-1)(2b-35)], both strictly negative. All roles fail
before later endpoint guards. Positive row scales preserve the linear
solve, multiply each quadratic by a positive product and cancel from
the solo ratio, so scales do not repair the failure.

For any proper nonempty child choose a retained owner whose cyclic
successor is omitted. Sole-owner sure stopping is exact child Nash;
every other retained owner's joining gap is negative. Its child debt
and Never vanish but the omitted successor has the positive gain above.
Every universal quiet-lift bound by weighted child debt plus Never fails,
for every child, weight and calendar. This does not exclude an adapter
supplied with a specially chosen safe child strategy. The toggle cycle
0->01->1->12->2->23->3->03->0 has positive gains
(1,1,1,3,1,1,11/10,3), excluding any global ordinal toggle potential.
These are complete tests of the stated raw selections, not a claim that
all nonstationary architectures or unspecified maximal neighborhoods fail.

## 7. A strict first-action-domain example

Use the literal four-player table Z(C) in the verifier below, for6<=C<=20.
Its own singletons are zero; original rewards are any nonnegative row raise.
It fixes Z1(02)=Z3(02)=14/25 and varies only
Z3(012)=Z1(023)=-1-C. Write odds(x,y,z,t), D=2+10(y+t)+yt. Then

    Phi0=-y+11t/10-Dz, Phi2=y-t-Dx,
    f=Phi1=x-3z+11xz/25-4t-t(x+z)/10+C*xzt,
    g=Phi3=-3x+z+11xz/25-4y-y(x+z)/10+C*xyz.

Pair02 alone has two positive participant premiums; its joining gaps -2,-2
give signed determinant-4. On013,123 owner3 has only nonpositive participant
premiums. On high012, R1=z(x-4)>0 gives x>4 and
D*f_y=4-261x/25+(761/25-44x/5)z<0 at fixed anchor levels.
On high023, R3=x(z-4)>0 gives z>4 and
D*g_t=41/10-261z/25+(7621/250-44z/5)x<0. Their transverse anchor determinant
is -D², so both signed triple determinants are negative, globally and for
all C. Every other proper-support high set is empty.

For full support R1=z(x-4)-t(1+x)(1+z)>0 and
R3=x(z-4)-y(1+x)(1+z)>0 force x,z>4. If Phi belongs to the payoff hull,
its anchor coordinates are at least-11. Since Phi0<=-2z,Phi2<=-2x and
Phi2<-8-39y-41t-4yt, the source odds belong to

    x,z in[4,11/2], y,t in[0,1/13].                    (B)

The following finite certificate excludes Phi from N1 on that entire box.
It uses conservative floors ell=(-11,-21,-11,-21)<=m(C), valid throughout
the interval. For each owner i index six polynomials by6i,...,6i+5:

    Q_i(q)-Phi_i, q_i(Phi_i-Q_i(q)),
    P_i(q)+ell_i H_i(q)-Phi_i, -R_i, ell_i-Phi_i, Phi_i-3.

The eight variables(q0,q1,q2,q3,x,y,z,t) range over[0,1]^4 times(B).
All24 polynomials are multiaffine in these separate variables and affine
in C. Each certificate word specifies successive lower/upper halves,
cycling axes0,...,7. Its nonnegative integer weights combine the indexed
polynomials. Every weighted vertex value divided by the weight sum is at
least9/30800. The33 prefix-free boxes cover the entire domain. The
standard-library verifier checks BOTH parameter endpoints; affine dependence
then proves every C in[6,20]. No numerical solver is used or trusted.

```python
from fractions import Fraction as F
from itertools import product
from math import prod,lcm

def table(C):
    return {1:[0,-1,3,-1],2:[-1,0,-1,3],4:[3,-1,0,-1],8:[-1,3,-1,0],
      3:[-2,0,0,F(-9,10)],5:[1,F(14,25),1,F(14,25)],
      9:[F(1,10),F(-9,10),0,-4],6:[0,-4,0,F(-9,10)],
      10:[-10,-1,-10,-1],12:[0,F(-9,10),-2,0],
      7:[-10,1,-10,-1-C],11:[-10,-1,-10,-1],
      13:[-10,-1-C,-10,1],14:[-10,-1,-10,-1],15:[-11,-1,-11,-1]}
proof=[
  ('00',{0: 53, 2: 587, 12: 360}),
  ('0100',{12: 19, 14: 181}),
  ('0101000000',{2: 930, 8: 29, 14: 40}),
  ('010100000100',{2: 577, 14: 64, 19: 158, 20: 201}),
  ('01010000010100000',{1: 212, 2: 199, 7: 147, 8: 74, 13: 290, 14: 14, 19: 29, 20: 35}),
  ('01010000010100001',{1: 57, 2: 6, 6: 43, 7: 119, 8: 8, 13: 46, 14: 36, 18: 271, 19: 405, 20: 10}),
  ('0101000001010001',{0: 15, 2: 127, 7: 858}),
  ('010100000101001',{0: 3, 2: 36, 7: 106, 12: 7, 19: 348}),
  ('01010000010101',{12: 15, 14: 127, 19: 858}),
  ('0101000001011',{2: 110, 7: 699, 19: 186, 20: 5}),
  ('01010000011',{1: 94, 2: 103, 6: 112, 7: 379, 8: 7, 13: 194, 19: 85, 20: 26}),
  ('0101000010',{2: 197, 8: 6, 14: 297}),
  ('0101000011',{1: 199, 7: 152, 8: 8, 13: 124, 14: 120, 19: 363, 20: 33}),
  ('01010001',{0: 40, 2: 55, 7: 708, 12: 20, 14: 177}),
  ('0101001',{0: 12, 2: 42, 7: 44, 12: 19, 19: 383}),
  ('010101',{0: 20, 2: 177, 12: 40, 14: 55, 19: 708}),
  ('01011',{7: 640, 12: 22, 14: 149, 19: 189}),
  ('0110',{2: 1}),
  ('011100000',{1: 129, 2: 98, 7: 475, 8: 32, 13: 115, 19: 151}),
  ('011100001',{1: 113, 2: 137, 7: 409, 13: 235, 19: 105}),
  ('01110001',{2: 34, 7: 91}),
  ('0111001',{2: 130, 7: 141, 19: 730}),
  ('011101',{2: 177, 12: 8, 14: 89, 19: 726}),
  ('01111',{2: 35, 7: 657, 14: 137, 19: 171}),
  ('10',{14: 1}),
  ('1100',{14: 1}),
  ('110100000',{1: 195, 7: 134, 13: 69, 14: 120, 19: 459, 20: 23}),
  ('110100001',{1: 266, 7: 61, 14: 196, 19: 465, 20: 12}),
  ('11010001',{0: 8, 2: 90, 7: 726, 14: 177}),
  ('1101001',{7: 39, 14: 129, 19: 832}),
  ('110101',{14: 34, 19: 91}),
  ('11011',{2: 101, 7: 697, 14: 62, 19: 140}),
  ('111',{1: 108, 2: 131, 7: 225, 13: 192, 14: 53, 19: 291}),
 ]
words=[s for s,_ in proof]
assert len(words)==len(set(words))==33
assert all(set(s)<=set('01') for s in words)
assert all(not t.startswith(s) for s in words for t in words if s!=t)
assert sum((F(1,2**len(s)) for s in words),F(0))==1
for C in[6,20]:
    Z=table(C);ell=[-11,-21,-11,-21];values=[]
    for bits in product([0,1],repeat=8):
        q=bits[:4];w=[4+F(3,2)*bits[4],F(bits[5],13),
                     4+F(3,2)*bits[6],F(bits[7],13)];row=[]
        for i in range(4):
            phi=F(0);R=F(0)
            for S in range(16):
                if S>>i&1:continue
                mon=prod(w[j] for j in range(4) if S>>j&1)
                R+=mon*Z[S|1<<i][i]
                if S:phi+=mon*(Z[S|1<<i][i]-Z[S][i])
            S=sum(q[j]<<j for j in range(4) if j!=i)
            Q=Z[S|1<<i][i];P=Z[S][i] if S else F(0);H=int(S==0)
            row.extend([Q-phi,q[i]*(phi-Q),P+ell[i]*H-phi,
                        -R,ell[i]-phi,phi-3])
        values.append(row)
    scale=lcm(*(F(v).denominator for row in values for v in row))
    base=[[int(values[k][i]*scale) for k in range(256)] for i in range(24)]
    for word,weights in proof:
        assert weights and all(0<=i<24 and type(v) is int and v>0
                               for i,v in weights.items())
        a=[sum(v*base[i][k] for i,v in weights.items()) for k in range(256)]
        for d,bit in enumerate(word):
            mask=1<<(7-d%8);out=[0]*256
            for k in range(256):
                if k&mask:continue
                L,R=a[k],a[k|mask]
                out[k],out[k|mask]=(2*L,L+R) if bit=='0' else (L+R,2*R)
            a=out
        assert F(min(a),scale*2**len(word)*sum(weights.values()))>=F(9,30800)
print('PASS:33 boxes, both endpoints, every C in[6,20]')
```

Midpoint restriction replaces arrays(L,R) by(2L,L+R) or(L+R,2R), doubling
the denominator. Thus the code is an exact finite polynomial proof. On a
diagonal kernel point every row is nonpositive, contradicting a positive
weighted combination. More generally the first-action inequalities(6) bound each row by maximum debt,
so every actual or limiting pair with U a full high Phi has debt>=9/30800.

There is ONE epsilon>0, uniform in C, for which full high Phi avoids
N1(C)+(-epsilon,epsilon)^4. Otherwise take C_k, high odds and u_k in N1(C_k)
with ||Phi_Ck(z_k)-u_k|| tending to0. Nearness to the hull gives anchor source
coordinates>=-12, hence x,z<=6 and39y+41t+4yt<=4. Extract all variables,
including kernel q and hull weights, on compact sets. The limit has
u=Phi in N1(C), R>=0, and its hull bounds sharpen the odds to(B), contrary
to the strict certificate. Therefore full orientation is vacuous on the
open tube, while the proper-support tests above hold globally. The open
source-domain consumer supplies A_Z=0 and UE under every nonnegative recipient-row raise.

For comparison, at C=6 and odds(41/10,1/1000,41/10,1/1000), all R_i>0 and

    Phi=(-82819041/10^7,-17689/25000,-82820041/10^7,-17689/25000),
    det D Phi=3379035934811871183/312500000000000>0.

This Phi is in the reward hull: positive weights on masks1,2,8,9,15 are
(15314359/5180000000,10166307917/77700000000,1482420491/38850000000,
46461077/518000000,9561662361/12950000000). They sum to1 and give that
exact reward average. Thus full weak orientation on the reward hull fails,
including every positive recipient scale and relabeling. This separates
this example from that raw criterion; no containment between standalone
criteria, or exhaustive exclusion of all other UE architectures, is claimed.

## 8. Formalization boundary and remaining cases

The new ordinary-mathematical obligations are the local zero-set induction
for arbitrary product words, the actual compact-minimum/repair consumer,
the raw first-action outer-set adapter, and weak orientation on the stated
domains. Relevant degree primitives are
`ambientDegree_homotopy` and
`ambientDegree_affineRootField_eq_sign_det` in
`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in `MathUE/Topology/AmbientDegreeProperties.lean`,
and `ambientDegree_of_selfMap_eq_one` in
`MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`.
The named terminal consumer fixes one uniform target before accuracy.
No new Lean check is asserted. Complete behavioral deviations and Never
are retained. The global source restriction does not assert realization
of a positive-debt cap as payoff, or an actual profile attaining a
zero-debt closure point. Tables failing the two raw orientation adapters
remain open; neither a positive-index root nor an auxiliary infeasibility
certificate settles arbitrary Fin4.
