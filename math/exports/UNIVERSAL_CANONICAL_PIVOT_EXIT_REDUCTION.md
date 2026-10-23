# A universal canonical pivot-exit reduction for four-player quitting games

## Exact statement

Let I={0,1,2,3}. For every nonempty S subset I, let Z_i(S) be a finite
real terminal reward. Assume Z_i({i})=0. Live play and literal AllNever
pay zero. Prescribed strategies use independent private randomization,
and a unilateral deviation may replace one player's entire behavioral
strategy. Along the unique unabsorbed history such strategies are
independent stopping laws on the natural dates and a separate Never point.

For an actual profile P, let U_i(P) be its expected terminal payoff and
B_i(P) the supremum over every unilateral replacement. Equivalently B_i
is the supremum over every finite deterministic deadline and Never. Set

    K=closure{(U(P),B(P)): P absorbs with probability one},
    d_i=B_i-U_i,       E=max_i d_i,
    g=min_(X in K) E(X),
    Gamma_ik=Z_i({k}),       Gamma_kk=0.

Fix M>=1 bounding all absolute rewards, so K is a nonempty compact
subset of [-M,M]^8, d_i>=0 and E<=2M. Suppose g>0. For e>=0 put

    C_e={X in K:min_i B_i(X)<=e},
    F_p={X in C_0:d_i(X)=0 for every i!=p}.

**Theorem 1 (every native positive-gap table).** For every prescribed player p
there exist a point X=(U,B)
in F_p, a number d=d_p(X), and an exact Nash root q of the finite binary
quitting game with continuation B, with the following properties.

1. The point X minimizes d_p on F_p and M>=d>=g>0. There is a sequence
   epsilon_n>0 tending to zero, genuine minima X_n of

       D_n=epsilon_n d_p+sum_(i!=p)d_i

   on C_(epsilon_n g/2), and nonzero nonsure exact roots q_n at B(X_n),
   such that X_n tends to X, q_n tends to q, min B(X_n)<=0,

       sum_(i!=p)d_i(X_n)/epsilon_n -> 0,
       W_(n,i)>epsilon_n g/2 for every i.

   Here W_n is the COMPLETE cap vector after the true q_n-prefix.

2. The limiting root is nonsure: c=product_i(1-q_i)>0. Its true
   successor lies in K and has debt c d e_p, where e_p is the coordinate
   unit vector. Exactly one of the following alternatives holds.

   **Positive-cap exit.** The root q is nonzero. Every successor cap W_i
   is strictly positive. Define

       r_p=max_(i!=p,Gamma_ip<0) [-Gamma_ip/(W_i-Gamma_ip)].

   The set is nonempty, 0<r_p<1, and

       r_p c d+(1-r_p)W_p>=d,
       W_p>d,
       U'_p>=(1-c)d/(1-r_p)>0.

   **Three-zero collapse.** The root q is AllContinue, and

       B=b e_p,       U=(b-d)e_p,       M>=b>=d>=g>0.

   For T=I minus {p}, every column h in T has both kinds of blocker:

       some i in T minus {h} has Gamma_ih<0;
       some j in T minus {h} has Z_j({j,h})-Gamma_jh>0.

   The witnesses i and j need not coincide. Moreover, either Gamma_T
   has a strictly positive off-diagonal entry, or it has the following
   exceptional form. All off-diagonal entries are nonpositive, exactly
   one row i has both off-diagonal entries zero, and, writing T={i,j,k},

       Gamma_jk<0,       Gamma_kj<0,
       min(Gamma_ji,Gamma_ki)<0,       Z_i({j,k})>0.

   For all sufficiently large n the pivot is inactive, q_(n,j)>0 and
   q_(n,k)>0, B_(n,j)>0 and B_(n,k)>0, while i is the unique nonpositive
   source-cap coordinate and

       -Z_i({j,k})q_(n,j)q_(n,k)/H_i(q_n)<B_(n,i)<=0,
       H_i(q)=product_(l!=i)(1-q_l)>0.

   In addition, the internal matrix G=Gamma_T is R0: the only vector
   v>=0 with Gv>=0 and v_i(Gv)_i=0 for all i in T is v=0. It also
   is either singular or has a strictly negative entry in its inverse.
   Both exclusions allow arbitrary joining and higher coalition rewards.
   In particular, if every row of G has a positive entry, then after
   cyclic relabeling its entries have the form

       G_(i,next(i))=-A_i<0,       G_(i,prev(i))=B_i>0,
       B_1 B_2 B_3<A_1 A_2 A_3.

   Its inverse is then strictly negative entrywise.

   Define the joining block by L_ij=Z_i({i,j})-Gamma_ij on T, with
   zero diagonal. It cannot have a strict cyclic ordering

       L_(i,next(i))=a_i>0,       L_(i,prev(i))=-b_i<0,
       product_i a_i<product_i b_i.

No ledger, coalition sign condition, supplied continuation, root selector,
or matrix condition is assumed. All strategic objects and the selected
minimum are produced from the finite table and its positive absorbing gap.

Call a native table joining-generic if all twelve off-diagonal joining
increments are nonzero and all four principal three-by-three joining
determinants are nonzero.

**Theorem 2 (generic exact exits and counterexample reduction).** If the
table is joining-generic, then for EVERY p there is a minimum X_p of d_p
on F_p and a nonzero nonsure exact root qhat_p at its full cap B(X_p).
The successor has every cap strictly positive, pivot debt c_p d_p with
0<c_p<1, and the positive-cap exit inequalities of Theorem 1:

    r_p c_p d_p+(1-r_p)W_p>=d_p,
    W_p>d_p,       U'_p>=(1-c_p)d_p/(1-r_p)>0.

The point X_p can be selected by Theorem 1's weighted minima. The root
qhat_p need NOT be the limit of their selected roots. Different p may
produce different points and roots.

Every native table with g>0 can be perturbed arbitrarily little to a
joining-generic native table still having g>0. Consequently an arbitrary
signed four-player no-UE table produces a native joining-generic table
with g>0 and the exact exits above for all four p. This is a reduction
to a necessary obstruction, not a claim that native AllNever fails Nash.

## Conjecture-facing change

An arbitrary signed four-player game without a uniform-equilibrium payoff
produces a native own-zero table with g>0, and a small perturbation makes
it joining-generic while retaining that gap. Every such table has the
canonical exact positive-cap exits in Theorem 2. Thus it suffices for
Fin4 to exclude these generic positive-cap exits for every chosen pivot;
the packet does not exclude them.

The underlying universal source theorem requires no genericity or ledger.
It excludes the one- and two-zero collapsed faces, the stated nonpositive
triple patterns, non-R0 principal singleton blocks, nonnegative inverses,
and strict joining cycles. Within strict singleton cycles it removes
the balanced and expanding side. Nongeneric source collapse may remain,
but it is no longer a separate obstruction in the generic counterexample
reduction. The full proof below distinguishes the original prelimit root
from a replacement exact root. No equilibrium or positive-gap example is
constructed.

Existence of an arbitrary one-debtor profile is not the claimed increment.
The selected minimum belongs to the absorbing carrier and the low-cap
face, retains the weighted prelimit roots, and has the o(epsilon_n)
control needed for the collapsed-face exclusions. Different pivots can
produce different points; the theorem does not combine their inequalities
at one common strategy profile.

## Strategic inputs and probability semantics

Finite mixed Nash existence supplies each auxiliary binary root. Compactness
selects the weighted minima and subsequences. Explicit finite prefixes and
their diffuse limits realize every comparison inside K. The proof assumes
no best-response attainer: a full cap is a supremum throughout.
The strict joining-cycle argument also uses the inverse-function theorem,
Banach's contraction theorem on a weighted sequence space, and ordinary
Brouwer degree with its homotopy and nonzero-degree existence properties.
The exact orbit construction and the degree computation are included below.

A behavioral strategy is determined on the only live public history by its
conditional quit probabilities. These probabilities define a private
stopping law; conversely every such law is implemented by its conditional
hazards. Thus an arbitrary replacement strategy averages the deterministic
deadlines and Never, and cannot beat their supremum. The laws are independent
across owners. No common randomizer, conditional correlation between players,
or execution of a compactified carrier point is used.

An element of K need not have a literal strategy realizer. Prefix maps
preserve K because the same finite prefix can be attached to each actual
absorbing member of a realizing sequence and because the full payoff/cap
map is continuous. A diffuse block means a limit of such actual prefixes,
not an infinite reversed calendar declared executable.

## Source correspondence

The actual finite-prefix cap formula is represented by
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
The exact cap-Nash contraction is
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
`UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`; the arbitrary-root
defect identity is
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.
The pair-valued prefix and its continuity are represented by
`quittingTerminalSemanticPair_rootThenContinuation` and
`continuous_quittingTerminalSemanticPrefix` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
The proof below includes the identities needed on the absorbing subcarrier.

The normalization input is
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.
The equivalence between no uniform payoff and a positive total-debt infimum
is `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`.
The finite-deadline limit used in the absorbing row shift is
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.

Existing weighted global-minimum budgets,
`minimumTerminalSemantic_weightedAuxiliaryNash_budget` and
`minimumTerminalSemantic_weightedSingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticWeightedAuxiliaryNashBudget.lean`,
minimize over the whole terminal semantic carrier. They do not already
supply the present low-cap absorbing minimum or its prelimit roots.
The exact finite-menu one-pivot sources in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`
concern a different strategy set and source selection. In particular
they supply neither minimization on F_p nor the strictly positive
successor caps W_n used here.

## Proof

### 1. Exact finite prefixes and their defect account

For q in [0,1]^4 let Q_i(q) be the Quit payoff against independent
opponent hazards q_-i, P_i(q) the passive payoff from their nonempty
quitting coalitions, and H_i(q)=product_(j!=i)(1-q_j). Define

    C_i(q;x)=P_i(q)+H_i(q)x_i,
    c(q)=product_i(1-q_i).

In the finite game with continuation x, owner i compares Q_i and C_i.
A root is nonsure when c(q)>0. It is AllContinue when q=0.
For a tail pair (U,B), prefix q and shift every tail clock by one date.
The prescribed payoff and complete cap are exactly

    U'_i=q_i Q_i+(1-q_i)[P_i+H_i U_i],
    B'_i=max(Q_i,P_i+H_i B_i).                         (1)

A pure response either quits at the new date or continues into one of
the entire old response laws. This proves the cap formula, including
Never and unattained response suprema. Both expressions are continuous.
Subtracting gives

    d'_i=c(q)d_i+rho_i(q;B),
    rho_i(q;B)=max(Q_i,C_i(q;B))
                   -q_i Q_i-(1-q_i)C_i(q;B)>=0.       (2)

Every exact Nash root at B has rho_i=0 for every i, so d'=c(q)d.
These statements pass to K by the realizing-sequence argument above.
In particular a sure exact root at any point of K would produce zero
debt in K, contradicting g>0.

### 2. Diffuse solo prefixes, including their finite collision caps

Let (U,B) belong to K with B>=0, fix owner k and r in [0,1]. For an
actual source delay all old clocks by N dates. Give k unconditional
quit mass a=(1-r)/N at each new date 0,...,N-1 and mass r on its
shifted old law. Every other owner uses its shifted old law. Conditional
hazards are a/(1-ta) before date t, so the construction uses independent
private laws on a deterministic calendar.

Writing P_ik=Z_i({i,k}) for i!=k, the prescribed payoff is

    U_k^r=rU_k,
    U_i^r=rU_i+(1-r)Gamma_ik for i!=k.                 (3)

Owner k has cap max(0,B_k)=B_k. For an outsider i, a pure deadline at
t<N gives exactly

    t a Gamma_ik+a P_ik.

If k quit earlier, i receives its passive singleton reward; if the two
quit at t, it receives P_ik; otherwise it quits alone for zero. Any old
response used after the block, including Never, has value
(1-r)Gamma_ik+r times its original response value. Consequently

    B_k^N=B_k,
    B_i^N=max(rB_i+(1-r)Gamma_ik,
                  aP_ik+(1-r-a)(Gamma_ik)_+)          (4)

for i!=k. This enumerates every distinct pure response alternative.
Since B_i>=0, the limit as N tends to infinity is

    B_k^r=B_k,
    B_i^r=max(0,rB_i+(1-r)Gamma_ik).                   (5)

The cap error is at most a|P_ik-(Gamma_ik)_+|. For a closure source,
first apply each finite continuous prefix to actual realizers and then
take the N-limit. Thus (3),(5) define a point of K.

Suppose B>0 and column k has a negative entry. Set

    r_k=max_(i!=k,Gamma_ik<0)
                    [-Gamma_ik/(B_i-Gamma_ik)] in (0,1). (6)

At r_k every affine outsider cap is nonnegative and at least one is
zero. No clipping has occurred, and

    d_k^r=r d_k+(1-r)B_k,
    d_i^r=r d_i for i!=k.                             (7)

The positive owner cap is paid for; its term (1-r)B_k is retained.

### 3. Seeds and negative singleton columns

Every C_e is nonempty. Let any owner k quit surely at date zero and let
all others play Never. The complete source data are

    U_i=Gamma_ik,
    B_k=0,       B_i=max(Gamma_ik,P_ik) for i!=k.       (8)

The outsider responses are Quit0, yielding P_ik, or any later deadline
and Never, yielding Gamma_ik. Owner k has only zero response values.
The profile absorbs surely and belongs to C_0.

Also g>0 forces a negative entry in every singleton column. Otherwise
let k use a fixed geometric hazard t>0 and all others play Never. The
profile absorbs surely, U_k=B_k=0, and U_i=Gamma_ik>=0. Against k a
deadline n has value

    Gamma_ik[1-(1-t)^n]+(1-t)^n t P_ik.

Its full cap, including Never, is max(Gamma_ik,tP_ik). Every debt
therefore tends to zero as t tends to zero, a contradiction.

### 4. Every positive weighted minimum supplies a nonzero exact root

Fix beta_i>0, write D_beta=sum_i beta_i d_i, beta_min=min beta_i and
beta_max=max beta_i, and choose 0<e<beta_min g/beta_max. Minimize D_beta
on C_e. Compactness supplies a minimizer X. It has min B<=0. Otherwise
choose k attaining 0<B_k=min B<=e. By Section 3 its column is eligible
for (6). The return (7) lies in C_0 and satisfies

    D_beta^r=rD_beta+(1-r)beta_k B_k<D_beta,

since beta_k B_k<=beta_max e<beta_min g<=D_beta. This contradicts
minimality.

If min B<0, take any finite Nash root at B. It cannot be AllContinue,
since a negative-cap owner could quit alone for zero. It cannot be sure
by (2) and g>0. Its true successor has debt c d with 0<c<1. If any
successor cap were at most e, it would lie in C_e and have a smaller
weighted objective. Therefore all successor caps are greater than e.

If min B=0, choose h with B_h=0 and, for small delta>0, take any Nash
root q_delta against the annotation x=B-delta e_h. It is nonzero because
x_h<0. Apply it to the ORIGINAL tail pair X. Only h's finite Continue
endpoint has changed, upward by H_h delta. At a best reply for x the
regret against B is at most q_h H_h delta. Thus (2) gives

    d_i^delta=c_delta d_i+Delta_i,
    Delta_i=0 for i!=h,
    0<=Delta_h<=q_h H_h delta=p_delta({h})delta.       (9)

For completeness, if q_h=0 its original Continue action remains best;
if 0<q_h<1 the old endpoints tied and its new regret is q_h H_h delta;
if q_h=1 the old Quit endpoint was at least Continue, so its new regret
is at most H_h delta. This proves the bound at every boundary root.

Choose delta<g and beta_h delta<D_beta. A sure root would give E_delta
at most delta<g, impossible. Since p_delta({h})<=1-c_delta,

    D_beta^delta<=c_delta D_beta
                    +(1-c_delta)beta_h delta<D_beta.  (10)

Consequently every cap of its true successor is greater than e. Extract
a root subsequence as delta tends to zero. Its limit is exact Nash at B
by continuity. It is not AllContinue: at q=0 the true cap map is
max(0,B)=B, with minimum zero, whereas the successor limits have every
cap at least e>0. It is not sure, because that would give zero limiting
debt in K. The limiting weighted objective is cD_beta<D_beta. Equality
of a limiting successor cap with e would again contradict minimality.
This proves in both cases a nonzero nonsure exact root with W_i>e.

Apply the owner-k first-zero return to this successor for ANY k. Its
weighted debt is r_k cD_beta+(1-r_k)beta_k W_k and it lies in C_e.
Minimality yields

    r_k cD_beta+(1-r_k)beta_k W_k>=D_beta,
    beta_k W_k> D_beta.                              (11)

All rewards used here may have arbitrary signs.

### 5. Concentration and exact pivot minimum

Choose any sequence epsilon_n in (0,1] tending to zero. Set beta_p=epsilon_n,
beta_i=1 for i!=p and e_n=epsilon_n g/2. Section 4 supplies minima X_n
and corresponding roots q_n. The owner-p instance of (11) gives

    D_n(X_n)<epsilon_n W_(n,p)<=epsilon_n M.           (12)

Take a subsequence for which X_n tends to X. Closedness gives X in C_0
and d_i(X)=0 for i!=p. Put d=d_p(X); then g<=d<=M.

For every Y in F_p, the same Y belongs to every C_(e_n). Hence

    epsilon_n d_p(X_n)+sum_(i!=p)d_i(X_n)
                         <=epsilon_n d_p(Y).         (13)

Dividing by epsilon_n and passing to the limit proves d<=d_p(Y).
Taking Y=X after its membership has been established also gives

    0<=sum_(i!=p)d_i(X_n)/epsilon_n
                         <=d-d_p(X_n) -> 0.          (14)

This proves the exact minimum and the stronger scaled concentration.

### 6. Limiting root and the positive-cap exit

Take a further subsequence with q_n tending to q. Each true successor
lies in K, so

    g<=c_n E(X_n)<=2M c_n.

Thus c=product_i(1-q_i)>=g/(2M)>0. The root limit is exact Nash at B,
its true successor has debt c d e_p, and W>=0. Dividing the owner-p
inequality in (12) by epsilon_n and using (14) gives W_p>=d.

If q is nonzero, then c<1. A successor with any nonpositive cap would
belong to F_p and have pivot debt c d<d, contradicting (13). Hence W>0.
The owner-p first-zero return is again in F_p, since every observer debt
stays zero. Applying the same minimum gives

    r_p c d+(1-r_p)W_p>=d.

As r_p>0 and c<1 this forces W_p>d. Since U'_p=W_p-cd, rearranging
also gives U'_p>=(1-c)d/(1-r_p)>0. This is the positive-cap exit.

### 7. Collapse has exactly three zero nondebtors

If q=0, its exact Nash property implies B>=0. The source lies in C_0,
and W_p=B_p>=d>0. Thus the nonempty zero set

    T={i:B_i=0}

contains only nonpivots. For every h in T, some other i in T has
Gamma_ih<0. Otherwise use (3),(5) for owner h with r<1 sufficiently
close to one. Every zero coordinate stays nonnegative, every positive
coordinate stays positive, and no affine cap is clipped. Owner h has
cap and debt zero. All other observer debts remain zero and pivot debt
becomes rd<d. The returned point is in F_p, a contradiction.

At every owner outside T, the prelimit finite Quit endpoint tends to
zero while its Continue endpoint tends to the strictly positive B_i.
Such owners are inactive for all sufficiently large n. At a nonsure
Nash root Continue is a best response for EVERY owner, active or not;
therefore

    W_(n,i)=P_i(q_n)+H_i(q_n)B_(n,i).                 (15)

If T were a singleton, P_i(q_n)=0 at its sole owner. Since every cap
outside T is eventually positive and min B(X_n)<=0, its source cap
would be nonpositive; (15) would contradict W_(n,i)>e_n.

If T={i,j}, the negative-column condition just proved gives
Gamma_ij<0 and Gamma_ji<0. The only possible passive terms are
Gamma_ij q_(n,j)<=0 and Gamma_ji q_(n,i)<=0. At least one source cap
in T is nonpositive, so (15) again contradicts W_n>e_n. Thus |T|=3.
Since I has four players, T=I minus {p}, and

    B=b e_p,       U=(b-d)e_p,       M>=b>=d>=g.

### 8. The nonpositive triple exception

Suppose all six internal off-diagonal entries of Gamma_T are nonpositive.
The pivot is eventually inactive. For i in T, let j,k be the other
two members. Its passive prefix polynomial is

    P_i(q)=Gamma_ij q_j(1-q_k)+Gamma_ik q_k(1-q_j)
                                    +Z_i({j,k})q_jq_k. (16)

If Gamma_ik=-a_i<0, dropping the other nonpositive singleton term gives

    P_i(q)<=q_k[-a_i+(a_i+M)q_j]<=0                  (17)

for every sufficiently small q. Thus at every row with a negative
entry, (15) and W_(n,i)>0 force B_(n,i)>0 eventually. Some source cap
in T must remain nonpositive. Its row therefore has both off-diagonal
entries zero. There cannot be two zero rows: the third column would
then have no negative entry, contrary to Section 7.

Write i for the unique zero row. Negative-column conditions imply
Gamma_jk<0, Gamma_kj<0 and min(Gamma_ji,Gamma_ki)<0. The only
nonpositive prelimit source cap is B_(n,i), and (16) reduces to
Z_i({j,k})q_(n,j)q_(n,k). Equation (15) with W_(n,i)>0 therefore
forces Z_i({j,k})>0, both hazards positive, and precisely

    -Z_i({j,k})q_(n,j)q_(n,k)/H_i(q_n)<B_(n,i)<=0.

If the internal singleton block is not nonpositive, it has a positive
entry, which is the other stated alternative. No compatibility or
impossibility claim is made about the exceptional case itself.

### 9. A positive joining increment in every zero-owner column

Fix h in the collapsed zero trio. Suppose
Z_i({i,h})-Gamma_ih<=0 for both i in T minus {h}. Prefix one literal
date at which only h quits, with probability t in (0,1). Owner h is
indifferent because B_h and its own singleton are zero. Each other zero
owner compares Q_i=tZ_i({i,h}) with C_i=tGamma_ih and optimally
continues. At the pivot, Continue minus Quit is

    (1-t)b-t[Z_p({p,h})-Gamma_ph]>0

for sufficiently small t. Thus this is an exact nonsure Nash root at B.
Its complete caps, payoffs and debts are

    W=(1-t)B+t Gamma e_h,
    U'=(1-t)U+t Gamma e_h,
    d'=(1-t)d e_p,       W_h=0.

Negative observer caps are allowed. The point lies in F_p with lower
pivot debt, a contradiction. Every zero-owner column therefore has the
claimed strict positive joining increment.

### 10. Strictly positive inverse blocks admit a pivot-debt return

Write G=Gamma_T and suppose G is invertible with G^(-1)>0 entrywise.
We construct a point of F_p with smaller pivot debt, without restricting
any higher coalition reward. The construction uses virtual observer
coordinates only to estimate finite prefixes of the actual closure source.

In every off-diagonal entry of GG^(-1)=Id, a positive linear combination
of the two off-diagonal entries in one row of G is zero. Neither can
vanish, since G has no zero row. Thus each row has opposite signs; the
identity G^(-1)G gives the same conclusion for columns. The positive
entries form a three-cycle. Relabel the observers cyclically as {1,2,3}
so that

    G_(i,next(i))=-A_i<0,       G_(i,prev(i))=B_i>0.

The diagonal cofactors are positive. Positivity of the diagonal inverse
entries therefore implies det G=B_1 B_2 B_3-A_1 A_2 A_3>0. Put

    rho=(B_1 B_2 B_3)/(A_1 A_2 A_3)>1.

Start a virtual observer payoff at x e_i. Prefix a solo macrostep by
owner next(i), with aggregate hazard q=x/(A_i+x). The moving owner has
payoff zero; coordinate i becomes zero and the third coordinate becomes
B_prev(i)x/(A_i+x). Three such steps, with movers 2,1,3 from x e_1,
return to that axis with amplitude

    F(x)=rho x/(1+C x),
    C=(A_2 A_3+A_2 B_3+B_2 B_3)/(A_1 A_2 A_3)>0.       (18)

Fix 1<r<rho. Choose a>0 so small that C a<=rho-r, and define x_0=a
and x_(n-1)=x_n/(rho-C x_n) for n<=0. Then
F(x_(n-1))=x_n and x_(-m)<=a r^(-m). All intermediate amplitudes
and hazards in a macrocycle starting from x e_1 are at most a fixed
constant times x, for x<=a. Hence the finite word from x_(-m) through
x_0 has total macrohazard at most a constant times a/(r-1), uniformly
in m. Its final macrocycle has fixed positive input x_-1, and therefore
has a fixed positive final hazard q_*>0. Shrink a until every macrohazard
is below 1/2 and twice their total is at most b/(16M).

These are algebraic prefix operations: the last operation constructed
is the first played chronologically. Every word is finite. No infinite
word in reverse chronological order is executed.

To control all observer responses, subdivide a macrohazard q into L
same-owner microhazards

    eta_l=q/(L-l q),       l=0,...,L-1,

with L large enough that every eta_l<=delta. Their survival product
is 1-q and their sum is at most q/(1-q)<=2q. During a partial macrostep
the accumulated hazard Q lies between zero and q. Its observer payoffs
are (1-Q)x-A_i Q>=0, zero at the mover, and B_prev(i)Q>=0. Thus all
virtual observer payoffs stay nonnegative at every microstep.

Start the virtual observer caps equal to their payoffs. Write their
debts as e_i. At a microstep by owner j, its own cap becomes max(0,B_j),
so its debt e_j>=0 is unchanged because its payoff is zero. For every
other observer, the full map (1) gives exactly

    e'_i=max(eta Z_i({i,j})-U'_i,(1-eta)e_i).

Since U'_i>=0 and eta<=delta,

    0<=e'_i<=max(M delta,e_i).

Consequently all virtual observer debts remain at most M delta through
the entire word, independently of its length. This controls complete
response caps, including collision rewards and every earlier deadline.

Give the virtual pivot its actual coordinates U_p=b-d and B_p=b.
It never quits in these prefixes. At a microstep by j its immediate
Quit endpoint is eta Z_p({p,j}), while its Continue cap is

    (1-eta)B_p+eta Gamma_pj.

As long as Continue has been selected, the pivot cap stays in [-M,M]
and each update changes it by at most 2M eta. The total microhazard is
at most b/(16M). Every Continue cap is therefore at least 7b/8, while
every Quit endpoint is at most b/16. Induction proves that Continue is
strictly optimal throughout. Its cap and prescribed payoff obey the
same affine update, and its debt at the end is exactly c_m d, where
c_m is the survival product of the macrosteps. Subdivision leaves it
unchanged. The product bound and the fixed final macrohazard give

    15/16<=1-b/(16M)<=c_m<=1-q_*<1.                  (19)

It remains to attach the word to the actual source. For a fixed root,
each payoff coordinate in (1) is Lipschitz with coefficient c<=1 in
its own continuation payoff, and each cap is Lipschitz with coefficient
H_i<=1 in its own continuation cap. These estimates persist through
every finite word. The virtual starting pair differs from X only by
x_(-m) in one observer's payoff and cap. Prefixing the same finite word
to X therefore gives a point X_(m,delta) of K satisfying

    |U_T(X_(m,delta))-a e_1|_infty<=x_(-m),
    |B_T(X_(m,delta))-a e_1|_infty<=M delta+x_(-m),
    0<=d_i(X_(m,delta))<=M delta+2x_(-m) for i in T.

The pivot coordinates agree exactly with the virtual computation: its
coordinate map depends only on its own continuation and the fixed roots.
Thus B_p>=7b/8 and d_p=c_m d. Let delta tend to zero along m tending
to infinity and extract a compact subsequence in K. The resulting point
Y has observer payoffs and caps exactly a e_1, pivot cap at least 7b/8,
and pivot debt c d with 15/16<=c<=1-q_*<1. It lies in F_p, has two
zero caps, and has strictly smaller positive pivot debt. This contradicts
the defining minimum and excludes G^(-1)>0 entrywise.

Every approximating endpoint was a finite prefix of actual absorbing
realizers. The virtual pair itself was not assumed to belong to K.

At the canonical source, this also rules out every NONNEGATIVE inverse.
If G^(-1)>=0, each row of G must contain a positive entry: otherwise
the corresponding diagonal entry of GG^(-1) could not equal one.
Section 7 supplies a negative entry in every column. These are at least
three positive and at least three negative entries among only six
off-diagonal positions. Consequently every row and column has one entry
of each sign, and all six entries are nonzero. Every cofactor of this
zero-diagonal three-by-three matrix is a signed product of two such
entries, hence nonzero. Thus its nonnegative inverse is strictly positive,
which has just been excluded. Every nonsingular surviving block therefore
has a strictly negative inverse entry.

### 11. The collapsed principal singleton block is R0

Suppose instead that G=Gamma_T has a nonzero vector v>=0 with

    Gv>=0,       v_i(Gv)_i=0 for every i in T.           (20)

Normalize sum_T v_i=1 and write A={i:v_i>0}. Fix 0<tau<=b/(16M).
For 0<epsilon<tau repeat the SAME product root

    q_i=epsilon v_i for i in T,       q_p=0

for K_epsilon=floor(tau/epsilon) finite dates, followed by the source X.
This finite prefix preserves K. Put c_epsilon=product_T(1-epsilon v_i).
Its one-row endpoints satisfy

    |P_i-epsilon(Gv)_i|<=2M epsilon^2 for i in T,
    |Q_i|<=M epsilon.

Indeed replacing singleton-event probabilities by epsilon v_j costs
at most M epsilon^2, while events with two or more opponent quitters
have probability at most epsilon^2/2. The second bound uses the zero
own singleton and opponent quit probability at most epsilon.

For an active observer i in A, (20) gives |P_i|<=2M epsilon^2.
Its prescribed one-row reward has magnitude at most 3M epsilon^2.
Starting from its zero source payoff and iterating (1) gives

    |U_i'|<=3M K_epsilon epsilon^2.

Every complete response that quits before the tail accumulates at most
K_epsilon passive contributions and one forced-Quit endpoint, each
multiplied by a survival probability at most one. A response continuing
into the tail has tail cap zero. Taking the supremum therefore gives

    |B_i'|<=2M K_epsilon epsilon^2+M epsilon,
    0<=d_i'<=5M K_epsilon epsilon^2+M epsilon.           (21)

This argument does not replace the active observer's opponent-survival
factor by c_epsilon: it bounds each term by its absolute magnitude.
It includes every finite tail deadline and Never, without requiring an
attaining response for the tail cap.

For an inactive observer i, q_i=0 and its opponent-survival factor DOES
equal c_epsilon. Also P_i>=-2M epsilon^2. Its prescribed payoff is

    U_i'=P_i sum_(s=0)^(K_epsilon-1)c_epsilon^s.

A forced deadline k before the tail has value

    V_k=P_i sum_(s=0)^(k-1)c_epsilon^s+c_epsilon^k Q_i,
    V_k-U_i'<=M epsilon+2M K_epsilon epsilon^2.

Continuing into the tail has response supremum U_i' because its old
full cap is zero. Hence every inactive observer likewise has
0<=d_i'<=M epsilon+2M K_epsilon epsilon^2. Its limiting payoff is
(Gv)_i(1-exp(-tau))>=0, while all active observer payoffs and caps tend
to zero by (21).

At the pivot, |Q_p|<=M epsilon. As long as Continue has been selected,
its cap stays in [-M,M], and each Continue update changes it by at most
2M epsilon. Since K_epsilon epsilon<=tau, induction keeps each Continue
cap at least b-2M tau>=7b/8. Every Quit endpoint is at most
M epsilon<=b/16. Thus the pivot strictly continues through the whole
word. Its payoff and full cap use the same affine update, giving exactly

    d_p'=c_epsilon^(K_epsilon)d -> exp(-tau)d<d.        (22)

Every endpoint belongs to K. A compact limit has zero observer debts,
at least one zero observer cap because A is nonempty, pivot cap at least
7b/8, and strictly smaller positive pivot debt. It belongs to F_p and
contradicts its minimum. Therefore G is R0.

This is a condition on the three-player PRINCIPAL block. Extending a
vector from (20) by v_p=0 need not yield a four-player complementarity
vector: the omitted coordinate sum_(j in T)Gamma_pj v_j may be negative.
The pivot's positive cap buffers that coordinate in the finite-prefix
construction. No full-matrix R0 implication is being assumed.

### 12. Exact remaining side of the strict signed-cycle class

Suppose every row of G has a positive entry. Together with the negative
entry in every column, this counts at least three positions of each sign
among six, forcing exactly one positive and one negative entry in each
row and column. Thus G has the signed-cycle form of Section 10. Its
adjugate is

    adj(G)=[ A_2 B_3   B_1 B_3   A_1 A_2 ]
           [ A_2 A_3   A_3 B_1   B_1 B_2 ]
           [ B_2 B_3   A_1 A_3   A_1 B_2 ],

and det G=B_1 B_2 B_3-A_1 A_2 A_3. Every adjugate entry is positive.
The case rho>1 therefore has strictly positive inverse and is excluded.
If rho=1, the vector v=(A_2/B_2,B_1/A_1,1) is a strictly positive
kernel vector, contradicting R0. Thus rho<1, proving the stated strict
product inequality and strictly negative inverse.

The exact scope of the homogeneous exclusion is useful here: under
the negative-column condition, NON-R0 occurs precisely at a balanced
strict signed cycle. Indeed a nonzero homogeneous complementarity
vector cannot have support one, since its column has a negative entry.
If its support is {j,k}, complementarity forces G_jk=G_kj=0. The
negative entry in each of these columns must then occur in the omitted
row i, giving (Gv)_i<0. Thus v has full support and Gv=0.

Every nonzero row must consequently have one positive and one negative
entry. A zero row i is impossible: column negativity forces G_kj<0
and G_jk<0, and the other two zero row sums against v>0 then force
G_ji>0 and G_ki>0, leaving column i without a negative entry. Hence
the matrix is a strict signed cycle, and its positive kernel forces
rho=1. Conversely rho=1 gives the positive kernel vector above.

These singleton restrictions alone leave contracting strict cycles and
matrices with at least one row having no positive entry. We next prove
the additional joining-cycle exclusion and the generic reduction.

### 13. A nonnegative singleton column anywhere in the pencil is impossible

Continue at a collapsed minimum X with observer set T. Put
G=Gamma_T, J_ij=Z_i({i,j}) for distinct observers, J_ii=0, and L=J-G.
Suppose for some owner j in T and 0<s<1,

    G_ij-s J_ij>=0 for both i in T minus {j}.           (23)

Fix a small f>0 and for n>=0 define

    R_n=f(1-s)^n,       S_n=1-f+R_n,
    r_n=R_n/S_n,        q_n=s r_n.

At chronological date n let only j quit, with hazard q_n. Then

    1-q_n=S_(n+1)/S_n,
    product_(n=0)^m(1-q_n)=S_(m+1),
    sum_(n>=0)q_n<=f/(1-f).                           (24)

Use the virtual observer pair whose payoff and cap at suffix n are
G_ij r_n for i!=j and zero for j. Against suffix n+1 the observer
Continue value is exactly G_ij r_n, because
q_n+(1-q_n)r_(n+1)=r_n. Its Quit endpoint is s J_ij r_n. By (23),
Continue is optimal. The moving owner j is indifferent at zero.
Thus this finite virtual computation has zero observer debt, including
when some virtual caps are negative.

For the word of dates 0,...,m initialize the pivot with its actual
payoff b-d and cap b at the terminal suffix. Choose f/(1-f)<=b/(16M).
As in Section 10, every pivot Continue-cap update changes it by at most
2M q_n, whereas its Quit endpoint is at most M q_n. Therefore its cap
stays at least 7b/8, it strictly continues, and its debt is S_(m+1)d.

Attach the same finite word to X. The virtual terminal observer pair
differs by at most M r_(m+1) from the zero actual source; the pivot
coordinates agree exactly. Coordinatewise nonexpansivity of (1) bounds
every final observer payoff and cap error by M r_(m+1). The endpoints
belong to K. Their compact limit has zero observer debts, observer j cap
zero, positive pivot cap, and pivot debt (1-f)d<d. It belongs to F_p,
a contradiction. This excludes (23), with weak inequalities included.

### 14. A positive expanding root orbit with a low-cap endpoint

We prove the full-support pencil consumer needed below. Assume L is
invertible, L^(-1) is strictly negative entrywise, and

    A v=rho v,       A=L^(-1)J,       v>0,       rho>1. (25)

Use roots supported on T, with the pivot always continuing. Near q=0
define observer vectors

    z_i(q)=[Q_i(q)-P_i(q)]/H_i(q),       s_i(q)=Q_i(q).

They are smooth, z(0)=s(0)=0, Dz(0)=L, and Ds(0)=J. The inverse-function
theorem gives a smooth local map F=z^(-1) composed with s, satisfying

    F(0)=0,       DF(0)=A,
    F(q)=Aq+R(q),       ||R(q)||<=C||q||^2.             (26)

Every sufficiently small strictly positive q is a fully mixed observer
root against continuation z(q), with new observer payoff and cap s(q).
The identity z(F(q))=s(q) therefore concatenates exact observer roots.

Here is a complete backward-orbit construction without a dominant,
simple, or nonresonant eigenvalue assumption. Choose rho<sigma<rho^2
away from the moduli of all eigenvalues of A. The real invariant spectral
splitting E_s plus E_f groups the eigenvalues below and above sigma.
There are equivalent block norms and numbers alpha_s<sigma<alpha_f with

    ||A_s||<=alpha_s,       ||A_f^(-1)||<=1/alpha_f.

For justification, when an operator has spectral radius below c, choose
a number beta between them. Jordan form bounds its powers by C beta^k.
The norm sum_(k>=0)c^(-k)||A^k x|| then makes its operator norm at most
c. Apply this separately to A_s and A_f^(-1); omit an empty block.

Let X_sigma be the Banach space of sequences x_n indexed by n<=0 with
norm sup_(n<=0)sigma^(-n)||x_n||. For forcing sequences f_n, n<=-1,
with the analogous norm, define the Green operator

    (Gf)^s_n=sum_(k=-infinity)^(n-1) A_s^(n-1-k) f^s_k,
    (Gf)^f_n=-sum_(k=n)^(-1) A_f^(n-1-k) f^f_k.

The fast sum is empty at n=0. The two geometric norm bounds are
||f||_sigma/(sigma-alpha_s) and ||f||_sigma/(alpha_f-sigma).
Thus G is bounded and direct cancellation gives

    (Gf)_(n+1)-A(Gf)_n=f_n for n<0.                   (27)

Put y_n=a rho^n v. On a fixed small neighborhood, smoothness also gives
||R(q)-R(r)||<=C' max(||q||,||r||)||q-r||. On the closed ball
||x||_sigma<=B a^2, with B a<=1, one has

    ||y_n+x_n||<=a(||v||+1)rho^n,
    ||R(y+x)||_sigma<=C(||v||+1)^2 a^2,

using sigma^n<=rho^n and rho^(2n)<=sigma^n for n<=0. Choose B larger
than twice the last fixed coefficient times ||G||. For sufficiently
small a, the map x -> G(R(y+x)) maps that ball into itself and has Lipschitz
constant at most ||G|| C'a(||v||+1)<1/2. Its fixed point gives

    F(q_n)=q_(n+1),
    q_n=a rho^n v+O(a^2 sigma^n) for n<=0.             (28)

Norm equivalence makes the error coordinatewise uniform. Since
(sigma/rho)^n<=1, choosing a small makes every q_n strictly positive,
every coordinate less than one, and

    sum_(n<=0)sum_i q_(n,i)<=C_0 a,
    sum_i q_(0,i)>=c_0 a>0.                           (29)

This proves the required orbit; only its finite segments are executed.

For each m start a virtual observer payoff/cap pair at z(q_-m), and
prepend q_-m,...,q_0 in that construction order. Every observer remains
exactly optimal, and its final payoff and full cap equal s(q_0).
Chronological execution is the reverse order of construction.

Give the pivot its actual pair (b-d,b), and choose a so that C_0 a<=
b/(16M). At a root with total observer hazard ell, its Quit endpoint
has magnitude at most M ell, while its Continue cap changes by at most
2M ell. The pivot cap thus stays at least 7b/8 and Continue is strictly
optimal throughout. Its debt is c_m d, where

    15/16<=1-C_0 a<=c_m<=product_i(1-q_(0,i))<1.       (30)

The low-cap requirement is essential. Since L^(-1)<0 entrywise and v>0,
Lv cannot be nonnegative: otherwise v=L^(-1)Lv<=0. Choose i with
(Lv)_i<0. Equations (25),(28) give

    s_i(q_0)=a(Jv)_i+O(a^2)=a rho(Lv)_i+O(a^2)<0       (31)

for fixed sufficiently small positive a. Thus the final virtual observer
cap has a strictly negative coordinate.

Attach the same finite word to X. Its terminal observer mismatch is
z(q_-m)=O(a rho^(-m)), and its pivot coordinates agree. Nonexpansivity
of the complete prefix maps bounds the final observer payoff and cap
errors by that mismatch. The endpoints lie in K; observer debts tend to
zero, the strictly negative cap in (31) persists, and the pivot debt has
a compact limit c d with 15/16<=c<1. The resulting point belongs to F_p
and has smaller pivot debt, a contradiction. This proves that (25) is
impossible under the stated sign of L^(-1). No virtual pair was assumed
realizable, and no infinite reversed word was executed.

### 15. Strict joining cycles are excluded by the entire pencil

Suppose the joining block is a strict cycle

    L=[0 a_1 -b_1; -b_2 0 a_2; a_3 -b_3 0],
    a_i,b_i>0,       Delta=product_i b_i-product_i a_i>0.

The adjugate formula in Section 12 applied to -L gives
(-L)^(-1)>0 entrywise, so L^(-1)<0. Also -L is R0. For a homogeneous
complementarity vector, a singleton support meets a negative column
entry. A support of size two is impossible because its principal
determinant is positive. Full support is impossible because det(-L)=
Delta>0. Thus all supports are excluded.

Consider M(t)=G-tJ for 0<=t<=1. Its endpoints are R0: G by Section 11
and M(1)=-L by the preceding paragraph. Suppose 0<t<1 has a nonzero
homogeneous complementarity vector x. A singleton support is excluded
by Section 13. For support {i,j}, the active equations force M_ij=
M_ji=0. In the remaining row k, M_ki x_i+M_kj x_j>=0 implies that
at least one of M_ki,M_kj is nonnegative. That column, whose other
exterior entry is zero, is a forbidden singleton column from Section 13.
For full support, M(t)x=0 gives

    L^(-1)Jx=[1/(1-t)]x,

which is excluded by Section 14. These cases exhaust the three-dimensional
supports, including zero exterior residuals. Hence every M(t) is R0.

We include the needed degree argument. For an R0 real matrix A define
f_A(x)=min(x,Ax) coordinatewise on R^3. Its only zero is zero, and positive
homogeneity gives ||f_A(x)||>=c_A||x|| for some c_A>0, by minimizing on
the unit sphere. Along the compact R0 path M(t), this bound is uniform.
Ordinary Brouwer homotopy invariance on a centered ball therefore gives

    degree_R0(M(t))=degree_R0(-L).                      (32)

The degree is independent of the radius by positive homogeneity. To
relate it to an arbitrary offset z, coordinatewise minimum is Lipschitz
in its second input, so

    ||min(x,Ax+u z)-f_A(x)||<=||z|| for 0<=u<=1.

On a ball of radius greater than ||z||/c_A this homotopy has no boundary
zero. Thus the offset map has the same degree as f_A. A nonzero degree
implies existence of x>=0 with Ax+z>=0 and x_i(Ax+z)_i=0. This is the
standard Q property, with arbitrary real offsets and no sign restriction
on z.

For A=-L and z=-one, empty and singleton supports cannot solve the
complementarity problem. A two-owner support would require both
off-diagonal entries of its principal block to multiply positive
coordinates to one, whereas those entries have opposite signs. The
unique remaining solution is x=(-L)^(-1)one>0. Near it the minimum map
equals -Lx-one and has local index sign det(-L)=+1. Computing degree
on a sufficiently large ball therefore gives degree_R0(-L)=1.
Equation (32) implies every M(t) is standard Q.

At any t, its Q property at offset -one supplies x>=0 with M(t)x>=one.
Thus every row has a positive entry. R0 forces every column to have a
negative entry, since otherwise its coordinate vector is a homogeneous
complementarity vector. The six off-diagonal positions must consequently
have one entry of each sign per row and column. Every x coordinate is
positive, since it is the sole positive contribution to some row. In
cyclic notation, the inequalities read

    d_i x_prev(i)>c_i x_next(i),       c_i,d_i>0.

Multiplying shows product d_i>product c_i. The explicit adjugate from
Section 12 is positive and the determinant is that positive product
difference. Hence M(t)^(-1)>0 entrywise, in particular G^(-1)>0.
Section 10 excludes this. The strict joining cycle is therefore
impossible, proving the last assertion of Theorem 1.

### 16. Generic tables force an exact positive-cap exit

Assume now that every off-diagonal joining increment is nonzero and
every principal three-by-three joining determinant is nonzero. Fix a
pivot and take its source from Theorem 1. A nonzero limiting root already
gives the desired exit. In the collapsed case, suppose for contradiction
that AllContinue is the ONLY exact finite root at B=b e_p.

Each column of L has a positive entry by Section 9. The matrix -L is
R0: support one is blocked by that positive entry of L; support two
would require a zero reciprocal entry, excluded by genericity; and full
support is blocked by det L!=0.

Fix any z in R^T. At annotations B+t z, extending z_p=0, choose finite
Nash roots q_t for t>0 tending to zero. Every cluster root is exact at
B, so uniqueness implies q_t tends to AllContinue. The pivot strictly
continues for all small t because its continuation cap tends to b>0,
while its Quit endpoint tends to zero. Every observer hazard is below
one. Its Continue-minus-Quit vector w therefore satisfies

    w=t z-Lq+O(||q||^2+t||q||)>=0,
    q>=0,       q_i w_i=0.                             (33)

Here q denotes the observer vector. These are the full active and
inactive finite Nash conditions: Continue is optimal for every observer,
and it ties with Quit at every positive hazard.

The ratios ||q||/t are bounded. Otherwise normalize by ||q|| along an
unbounded subsequence and pass to a limit on the unit sphere. Equation
(33) would give a nonzero v>=0 with -Lv>=0 and v_i(-Lv)_i=0,
contradicting R0. Taking a cluster limit x of q/t and dividing (33)
by t now gives

    x>=0,       -Lx+z>=0,       x_i(-Lx+z)_i=0.

Since z was arbitrary, -L is standard Q. In particular z=-one gives
-Lx>=one. Each row of L therefore has a negative entry; each column
already has a positive entry. Counting the six positions forces a
strict signed cycle L_i,next(i)=a_i>0, L_i,prev(i)=-b_i<0. Every
coordinate of x is positive, and its three inequalities imply
b_i x_prev(i)>a_i x_next(i). Multiplication gives product b_i>
product a_i. Section 15 excludes precisely this strict joining cycle.

Therefore B has some nonzero exact root qhat. It is nonsure because
an exact sure root would create zero debt in K. Its successor debt is
c d e_p with 0<c<1. Any nonpositive successor cap would return to F_p
with smaller debt, so every successor cap is positive. Its pivot-only
first-zero return is in F_p, and the argument of Section 6 gives all
three exit inequalities. This root need not be the limit of the original
weighted prelimit roots. This proves the exact-exit part of Theorem 2.

For the perturbation assertion, if two native tables differ by at most
eta in every terminal reward, every fixed actual prescribed payoff and
every pure-response payoff differ by at most eta. Their full caps
differ by at most eta, hence their maximum debts differ by at most 2 eta.
The set of absorbing profiles is independent of the reward table.
Taking infima over that same set gives

    |g_Z-g_Ztilde|<=2||Z-Ztilde||_infty.                (34)

Thus g>0 persists on an open neighborhood of the native table. Vary
only the twelve recipient rewards Z_i({i,j}), i!=j, leaving all singleton
and other rewards fixed. These coordinates change the twelve joining
increments independently. The product of all twelve increments and the
four principal triple determinants is a nonzero polynomial: assigning
every joining increment the value one makes every triple determinant
equal to two. Its nonvanishing set is dense, because a nonzero real
polynomial cannot vanish on an open ball. Arbitrarily small perturbations
therefore satisfy the stated genericity conditions and retain g>0 by
(34). Combining this with the adapter below completes Theorem 2.

## Adapter from an arbitrary signed Fin4 counterexample

Suppose an arbitrary signed reward table r has no uniform-equilibrium
payoff. A finite absolute reward bound exists. Applying
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` produces
a literal table R with own singleton vector e_m for some player m,
zero AllNever payoff, and no uniform-equilibrium payoff. Its source
also supplies the punishment-normal assumptions needed by the checked
normalization and reverse lift; no arbitrary affine invariance is used.
The checked total-debt-infimum equivalence gives

    delta=inf_(P actual) sum_i d_i^R(P)>0.

Define Z_i(S)=R_i(S)-1_(i=m) for EVERY nonempty coalition S, retaining
zero at AllNever. Then Z has own singleton zero. Both R and Z have
nonnegative own singletons. For either table, a forced finite deadline
tending to infinity has payoff tending to

    payoff(Never)+own_singleton_i * product_(j!=i)N_j.

Here N_j is the opponent's actual Never mass. Bounded convergence proves
the identity: on an opponent finite quit, the delayed response eventually
receives the Never payoff; on the all-opponent-Never event it receives
its own singleton. Consequently the supremum over finite deadlines
already dominates Never before and after the row shift.

On an absorbing PRESCRIBED profile, the pivot payoff shifts down by one.
Every forced finite response also absorbs, so each such response payoff
shifts down by one. Taking their suprema shows that the pivot's complete
cap shifts by one as well. All four debts are therefore unchanged on
every absorbing prescribed profile. Thus

    inf_(P absorbing) sum_i d_i^Z(P)>=delta,
    g_Z=inf_(P absorbing) max_i d_i^Z(P)>=delta/4>0.

Continuity identifies the latter infimum with the minimum on K. This
supplies every hypothesis of Theorem 1. Section 16 then perturbs the
native table arbitrarily little to make it joining-generic while keeping
its absorbing gap positive, supplying Theorem 2. The normalization player
m need not equal the freely selected pivot p in either theorem.

The native table Z is not asserted to lack a uniform payoff: its
AllNever profile is exact Nash. Positive gap is asserted only on its
absorbing carrier. No row-shift identity for prescribed profiles with
positive joint Never is required or claimed.

## Boundary tests

**The owner charge cannot be deleted.** Set all unlisted rewards to zero,
and prescribe

    Z_1({0})=-1,       Z_0({1})=-1,
    Z({0,1})=(1,1,0,0).

Let owners 0 and 1 quit surely at date zero and let owners 2 and 3
play Never. The actual full pair is U=B=(1,1,0,0). Apply a diffuse
solo-0 prefix with r=1/2. Equations (3)--(5) give

    U^r=(1/2,0,0,0),       B^r=(1,0,0,0),
    d^r=(1/2,0,0,0).

For N equal unconditional atoms, B_1^N=1/(2N); every other displayed
cap is already exact. Thus the first-zero return exists in K but pays
the positive owner cap. An unjustified debt-contraction formula would
falsely preserve the original zero debt on this example.

**Actual partial Nash and low cap do not imply the selected exclusions.**
Again set all unlisted rewards to zero, and prescribe

    Z_1({0})=1,
    Z({0,1})=(0,1,1,0),
    Z_2({0,1,2})=1,       Z_3({0,1,3})=1.

With owners 0 and 1 surely quitting at zero and the others using Never,

    U=(0,1,1,0),       B=(0,1,1,1),       d=e_3.

Every unilateral replacement still faces a different sure quitter, so
Quit0 and a later deadline/Never exhaust all response values. The source
has one zero cap and exactly one positive debt. However all four owners
quitting at zero is an exact zero-debt profile, since every grand and
passive-triple reward is zero. Hence g=0, and the displayed source is
not the minimum selected by the theorem. Actual feasibility and debt
concentration alone do not supply its positive-gap and prelimit provenance.

**Missing negative column.** If all outsider entries in one singleton
column are nonnegative, the exact geometric calculation in Section 3
constructs absorbing profiles with E tending to zero for arbitrary
higher rewards. Thus g>0 cannot survive that boundary. This tests the
eligibility premise used by every first-zero return.

**Expansion has a strict boundary.** For the internal singleton block

    G=[0 -1 2; 2 0 -1; -1 2 0],

the inverse is (1/7)[2 4 1;1 2 4;4 1 2], rho=8, C=7, and the
macrocycle is F(x)=8x/(1+7x). The cycle calculation and fixed final
hazard are exact. Replacing every positive entry 2 by 1 makes G singular
and rho=1. The expanding backward chain then fails; Section 10 does
not exclude that balanced boundary. It is instead excluded by Section 11,
because v=(1,1,1)/3 is a nonzero homogeneous complementarity vector.
The cycle proof permits arbitrary signed joining rewards by subdivision,
rather than asserting exact observer Nash behavior at a finite mesh.

**Principal R0 is a separate constraint.** Take the balanced internal
block G=[0 -1 1;1 0 -1;-1 1 0] and give every singleton entry between
the pivot and an observer the value -1, in both directions. The full
four-player singleton matrix is R0: for any nonnegative homogeneous
complementarity vector, its pivot inequality forces all three observer
coordinates to vanish, and then the observer inequalities force the
pivot coordinate to vanish. Yet G itself is not R0, as witnessed by
v=(1,1,1)/3. Thus a full-matrix R0 test cannot replace Section 11's
principal-block exclusion. No positive-gap game is claimed by this
matrix-only boundary example.

**The expanding-ray endpoint must remain in the low-cap set.** With
L=[0 1 -2;-2 0 1;1 -2 0], J=2L and G=J-L=L, the vector v=one
satisfies L^(-1)Jv=2v, Lv=-one and Jv=-2one. Thus the endpoint in
Section 14 is -2a one+O(a^2), strictly negative for fixed small a.
This checks the sign that makes the new pivot-debt consumer return to
F_p. A merely positive survival drop with all endpoint caps positive
would not contradict its constrained minimum.

**Genericity preserves the obstruction only through the gap estimate.**
All twelve joining increments equal to one make each principal triple
determinant exactly two, so the polynomial used in Section 16 is nonzero.
Equation (34) preserves a given positive gap under a perturbation smaller
than g/2. It does not identify the original and perturbed minima, transport
their selected roots, or assert that the perturbed native table lacks UE.

These are boundary and falsification tests of the proof. No example of
a game with g>0 is claimed.

## Adapter, remaining consumer, and Lean handoff

The actual-data chain is arbitrary signed no-UE data, the checked
single-pivot normalization, the proved absorbing row shift, a small generic
pair-reward perturbation preserving the absorbing gap, and the fully
produced canonical exact positive-cap exits. The missing consumer is a
contradiction to these exits, or an absorbing approximate-equilibrium
construction on every generic table admitting them. There is an exit
for each prescribed pivot, but their sources need not coincide. No such
consumer is assumed as a field of the source record.

A formalization can introduce the closure of absorbing payoff/full-cap
pairs and its low-cap subsets, reusing the continuous finite prefix.
The new ordinary-mathematical lemmas to implement are: the finite diffuse
cap formula and its limit; first-zero weighted return; weighted low-cap
minimum root production including the tied perturbation; concentration
with o(epsilon_n) observer debt; the Fin4 collapsed-face exclusions; and
the finite subdivided expanding-cycle and homogeneous-direction returns
with a positive pivot cap. The stronger generic endpoint additionally
needs the exact singleton bursts, the positive backward-orbit lemma and
its negative-cap endpoint, the three-dimensional pencil degree argument,
the unique-root-to-Q scaling argument, and the reward perturbation estimate.
The source statement should quantify over the finite native reward table
and g>0, and conclude existence of the minima, root sequences, and generic
replacement exits. It should not accept them as unproved structure fields.

Finite arithmetic tests can check (1), (4), and the two sparse boundary
tables. Compactness and limit arguments require proofs, not numerical
surrogates. Existing whole-carrier weighted-budget declarations are
useful comparisons but their global-minimum hypothesis must not be
silently applied to C_e or F_p. The same caution applies to diagonal
least-Never sources: here U_p and B_p differ by d>0.

This packet asserts ordinary mathematics for unrestricted independent
behavioral deviations. It does not assert a new checked Lean theorem,
resolve Fin4, identify a positive-gap reward table, or turn a bounded
strategy search into an unrestricted counterexample.
