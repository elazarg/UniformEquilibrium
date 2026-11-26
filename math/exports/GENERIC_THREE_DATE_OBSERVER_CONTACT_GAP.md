# Generic low-support calendars have a quantitative observer-contact gap

This is an ordinary mathematical source restriction, not a proof of the
four-player quitting-game conjecture or a Lean-checked theorem. It applies
to finite chains of independent product roots, including those from actual
stopping laws, and supplies its finite rank condition from an explicit
nonzero polynomial in the raw rewards.

## Statement

Let I={0,1,2,3}. A native quitting table assigns finite real rewards Z_i(S)
to every nonempty coalition S, with Z_i({i})=0 and AllNever payoff zero.
Players independently choose complete laws on the natural dates and Never.
At each live date let q_i be the conditional quitting hazard, e_i the payoff
from Never, and Q_i the payoff from quitting immediately. Write

    Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}) for i!=j,
    Gamma_ii=J_ii=0.

Let U_i be prescribed expected payoff and B_i the supremum over every
unilateral behavioral replacement. ALL-END means B_i=e_i for every player;
observer optimality means U_i=B_i for every observer.

There is an explicit nonzero homogeneous integer polynomial P of degree5184
in the24 off-diagonal coordinates of Gamma,J with the following property.
The other32 finite native reward coordinates are unrestricted.

If P(Gamma,J)!=0, then, for each pivot p and its three observers I\{p},
there are constants h,c>0 with the following property. Take any three
product roots q_0,q_1,q_2 in[0,1]^4 and any terminal observer vector
E(3) in R^3. Propagate E backwards by

    E_i(k)=A_i(q_k)+H_i(q_k)E_i(k+1),                    (0)

where A_i is the absorbing Continue contribution and H_i the opponents'
survival probability, defined explicitly below. The conditions

* each date has at most two players with positive hazard;
* its maximum hazard eta satisfies 0<eta<h;

imply

    max_(date k, observer i) |Q_i(q_k)-E_i(k)| >= c eta.   (1)

The constants depend on the fixed finite table, not the roots or the size
or meaning of the terminal vector. No actual realization is needed for
this finite assertion. In particular no such window can have all three
observers tied, Q_i=E_i, at all three dates. The support
pairs may change arbitrarily, need not contain the pivot, and may be
singletons padded by a zero coordinate.

For an actual law with positive survival to a window entrance, take E_i(k)
to be its actual conditional Never payoff e_i(k). The result applies to
every consecutive three-date window, also after deleting empty dates.
If every original marginal Never mass is positive, hazards tend to zero.
Consequently (1) holds on every sufficiently late such window. If the actual
profile is ALL-END and every observer is optimal, then Q_i<=e_i everywhere
and equality holds at every positive observer hazard. In that case (1)
produces an INACTIVE observer whose strict slack e_i-Q_i is at least c eta.
Thus every sufficiently late three-date low-support window with eta>0 contains a
quantitatively strict quiet comparison.

No minimizing assumption, pivot-contact restriction, uniform hazard ratio,
or hypothesis on the later support calendar is required. No claim is made
that every sparse date is guarded: the conclusion supplies one strict
quiet comparison somewhere in each triple.

The set P!=0 is open dense in the full24-dimensional raw coordinate space.
It can therefore be imposed by an arbitrarily small native reward
perturbation preserving any supplied positive absorbing gap, before a
source is selected afresh. This last statement concerns the absorbing gap;
native AllNever itself is an exact Nash profile.

The finite table is the only input to the contact test and its constants.
The inverse matrices and the elementary root formulas produce h,c; no
continuation selector, improving strategy, or correction oracle is supplied
as a hypothesis. The conjecture-facing consequence is a restriction on
every actual source at the generically selected table. Actual realization
of a compact source and the existence of an observer-constrained minimum
are separate obligations. The algebraic assertion also applies to a
nonrealized semantic root chain whenever its three observer caps follow
the Continue branch (0). It does not produce such a chain. The theorem
leaves all size-three and size-four supports, and sparse triples with some
strict quiet slack, available.

## Complete-law semantics and the local equations

A behavioral strategy along the unique unabsorbed public history defines
a private stopping law. Conversely its conditional hazards implement any
complete law. Fixing a deviator's private randomness gives a deterministic
deadline or Never, so its unrestricted behavioral cap B_i is the supremum
of those responses, including Never; no best-response attainment is assumed.

For a root q set H_i(q)=product_(j!=i)(1-q_j), and for S subset I\{i} put

    pi_i(S;q)=product_(j in S)q_j product_(j notin S,j!=i)(1-q_j),
    Q_i(q)=sum_S pi_i(S;q) Z_i(S union{i}),
    A_i(q)=sum_(nonempty S) pi_i(S;q) Z_i(S).

The exact pure-Never and full-cap recursions are

    e_i(k)=A_i(q_k)+H_i(q_k)e_i(k+1),
    B_i(k)=max(Q_i(q_k), A_i(q_k)+H_i(q_k)B_i(k+1)).       (2)

Finite rewards and native own-singleton zero give, for small q,

    Q_i(q)=J_i q+O(|q|^2),
    A_i(q)=Gamma_i q+O(|q|^2),  H_i(q)=1+O(|q|).          (3)

The constants in these finite polynomial bounds depend only on the table.
Deleting an empty date leaves every retained Never offer and Quit offer
unchanged, so (2) also holds on the compressed calendar.

For the finite chain (0), let eta be its maximum hazard and put

    tau=max_(k=0,1,2; i!=p)|Q_i(q_k)-E_i(k)|.

Equations (3) give E_i(k)=J_i q_k+O(eta^2+tau) on these three
dates. For k=0,1, equation (0) therefore yields

    E_i(k+1)=E_i(k)-Gamma_i q_k+O(eta^2+eta tau).          (4)

Only the next observed cap occurs in this estimate; it is already bounded
by O(eta+tau). No estimate comparing a later pivot cap or total future mass
to the current window activity is being assumed.

For positive original marginal Never masses N_i, one has
product_t(1-q_i(t))=N_i>0, hence sum_t q_i(t)<infinity and q_i(t)->0.
This is the only tail fact needed for the late-window conclusion.

For the observer-optimal corollary, positive original Never gives positive
survival to every finite cut. ALL-END and observer optimality pass to each
actual conditional tail: any strict improvement after that cut would give
a strict initial improvement. Equation (2) gives Q_i<=e_i, and the exact
prescribed-payoff recursion shows that a positive observer hazard can be
optimal only when Q_i=e_i. Hence a strict gap supplied by (1) belongs to an
inactive observer.

## The finite contact matrix and its quantitative consequence

First fix p=0. Let K be the six unordered pairs of players, each written
in increasing order. For a word w=(S_0,S_1,S_2) in K^3 introduce nine
variables: three entrance observer caps z_1,z_2,z_3, and the six controls
q_(k,j) for j in S_k. Other current hazards are zero. Define the9-by9
matrix M_w(Gamma,J) by the nine linear forms

    z_i - sum_(l<k) sum_(j in S_l) Gamma_ij q_(l,j)
        - sum_(j in S_k) J_ij q_(k,j),
                 k=0,1,2 and i=1,2,3.                  (5)

The first three columns are constants and the other six are linear in
Gamma,J. Thus det M_w is a homogeneous integer polynomial of degree six
whenever it is nonzero. Define

    P_0(Gamma,J)=product_(w in K^3) det M_w(Gamma,J).      (6)

There are216 words, with no restrictions on repeated or changing supports.
The explicit exact calculation below gives one integer matrix pair for
which EVERY determinant is nonzero, their minimum absolute value being12.
Thus P_0 is a nonzero polynomial of degree1296.

For general p define P_p by relabeling p as0 and its observers as1,2,3.
The choice of observer ordering only changes harmless determinant signs.
Each P_p is nonzero, because relabeling is an invertible coordinate
permutation. The real polynomial ring is an integral domain, so

    P=product_(p in I) P_p                              (7)

is nonzero and has degree5184. Its nonvanishing is precisely the simultaneous
invertibility of all the matrices needed here for every pivot. A nonzero
real polynomial has no open zero set; consequently P!=0 is open dense.

Fix a table with P!=0 and a pivot. The finite collection of216 inverse
matrices has a finite maximum norm L. Pad every support of size less than
two to an arbitrary pair, setting the extra controls equal to zero.
Let X collect its three entrance coordinates E_i(0) and six padded controls.
Using (4) to eliminate the two intermediate caps, and (3) to express each
contact residual, gives

    |M_w X| <= C(eta^2+tau+eta tau).                     (8)

Since eta is one of the control magnitudes, inversion gives

    eta <= LC(eta^2+tau+eta tau).

For eta<=1 absorb 1+eta into the tau coefficient. Choose h>0 so small
that LC h<=1/2, decreasing it if necessary for (3). Then
eta/2<=2LC tau. Taking c=1/(4LC), or any smaller positive constant,
proves (1). This also proves the exact-contact exclusion when tau=0.
No sign of a cap or reward was used, and singleton padding introduced no
positivity assumption on the added coordinates.

## A retained-Never corollary for possibly nonrealized chains

The late-window conclusion has a purely algebraic extension. Suppose an
infinite supplied sequence of roots q_k and observer vectors E(k) satisfies
(0), Q_i(q_k)<=E_i(k), and equality whenever the observer hazard q_i(k)>0.
Suppose it also retains coordinates N_i(k) in[0,1] with N_i(0)>0 and

    N_i(k)=(1-q_i(k))N_i(k+1) for every player and date.

Iteration gives

    product_(k<n)(1-q_i(k))=N_i(0)/N_i(n)>=N_i(0)>0.

In particular every N_i(n)>0, every q_i(k)<1, and sum_k q_i(k)<infinity.
Thus all sufficiently late three-date support-at-most-two windows with
eta>0 obey (1), with a strict slack E_i-Q_i>=c eta at an inactive observer. Empty
roots may again be deleted, because both E and N are unchanged there.
This conclusion holds even if the supplied vectors have no actual
infinite-law realization and no terminal vector limit is known.

For a semantic cap chain the hypotheses mean that each observer selects
Continue at every root, and every positive observer hazard is tied.
They follow from observer optimality at consecutive semantic pairs and
q_i(k)<1: prescribed payoff is the convex combination of Q_i and
A_i+H_i B_i(k+1), while the full cap is their maximum. Equality of payoff
and cap forces the Continue endpoint to attain that maximum, and also the
Quit endpoint whenever q_i(k)>0. Thus this version needs no ALL-END
hypothesis and applies to observer-optimal nonsure prefix chains.
The corollary is a restriction on such supplied chains, not a construction
of a chain from an arbitrary compact source. Retained positive Never is
used to force small late roots; a scalar survival annotation without
the stated recursion and bounds cannot replace it.

## Generic selection preserves a supplied absorbing gap

For a native table Z define

    g(Z)=inf_(P absorbs almost surely) max_i [B_i^Z(P)-U_i^Z(P)],

where every prescribed profile is actual and each cap allows all unilateral
behavioral deviations, including Never. Equivalently take the minimum
over the compact closure of the associated payoff/cap pairs.

If ||Z-Z'||_infinity<=delta, every prescribed or deviated expected terminal
payoff changes by at most delta, using the same outcome law. Suprema of
deviation payoffs also differ by at most delta. The class of absorbing
prescribed profiles is independent of rewards. Taking maxima and infima
therefore gives

    |g(Z)-g(Z')|<=2delta.                                (9)

If g(Z)>0, choose a raw24-coordinate perturbation of norm less than g(Z)/4
with P!=0, leaving the other32 rewards and all own singletons unchanged.
Density supplies such a choice, and (9) gives g(Z')>=g(Z)/2>0. It can also
be chosen inside any already required open reward conditions or any finite
intersection of other nonzero-polynomial conditions in the same varied24
coordinates.

All source objects must then be selected afresh at Z'. Neither an old law
nor an old minimizing point is transported across the perturbation. Any
actual positive-Never, ALL-END, observer-optimal source selected at the new
table has the quantitative quiet-contact property (1). This theorem does
not itself prove existence or actual realization of that source.

For context, an arbitrary signed Fin4 counterexample produces the required
native positive absorbing gap as follows. The checked single-pivot
normalization supplies a table R with own singleton vector e_m, zero
AllNever, and no uniform-equilibrium payoff. The positive terminal-gap
equivalence supplies delta>0 with sum_i d_i^R(P)>=delta for every actual P.
Set Z_i(S)=R_i(S)-1_(i=m) for every nonempty S, retaining zero at AllNever.
The resulting table has own singleton zero. For R and Z, every own singleton
is nonnegative, so a deterministic deadline tending to infinity has payoff
converging to the Never payoff plus own_singleton_i times the opponents'
joint Never mass. Consequently the supremum over finite deadlines already
dominates Never. On every absorbing prescribed profile, the pivot payoff
and every finite-deadline pivot response both decrease by one; hence its
full cap also decreases by one. All four debts remain unchanged there.
Thus g(Z)>=delta/4>0, and (9) permits the generic selection above.

The native table is not asserted to lack a uniform-equilibrium payoff:
AllNever is exact Nash. The preserved obstruction is its positive gap on
absorbing prescribed profiles. Compact source points without a supplied
chain as above, supports of size three or four, and sparse windows with
only partial observer contact remain outside the exclusion.

## Boundary tests

The degeneracy restriction is necessary. At the all-zero table every Quit
offer and Never offer is zero. For example, let players0,1 both have hazard
2^(-t-3) at date t, and let players2,3 always Continue. These complete laws
have positive original Never, infinitely many pair dates, and exact contact
for all observers at every date. Thus the conclusion fails outside the
generic set. In the other direction, the integer matrices in the certificate
give an explicit point where all216 fixed-pivot determinant factors are
nonzero; their sole role is to prove the raw polynomial condition is
nonvacuous, not to exhibit a positive-gap game.

Three dates are the first possible length for this uniform injectivity
argument on arbitrary pair supports. Two dates supply six observer contact
equations in seven variables: three entrance caps and four controls.
Their matrix always has a nonzero kernel, and a nonzero kernel vector has
some nonzero control because zero controls force all entrance caps to zero.
This is a dimension limit of the matrix argument, not an assertion that
every such two-date kernel has nonnegative hazards or an actual realization.

## Native source correspondence

The definitions `quittingStoppingLawExpectedPayoff` and
`quittingStoppingLawReplacementPayoffCap` are in
`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
The declarations
`quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`
and `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
identify their values with unrestricted behavioral semantics. Conversely,
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
give these identities for the conditional-hazard implementation of complete
independent laws.

The literal root identity is
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, and its full-cap
maximum formula is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.

The counterexample normalization used above is
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.
The terminal-gap equivalence is
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap` in
`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.
These exact statements were inspected. They provide the original-game
semantic adapter, not a Lean proof of the new contact polynomial or (1).

For a Lean implementation, define the nine-variable contact matrix over the
six-pair word type and prove its entries from the literal Never recursion.
Formalize the216 exact determinant checks and the relabeling construction
of P. The nonlinear step needs only finite polynomial remainder bounds and
the finite maximum inverse norm; it does not require an implicit-function
theorem or an infinite-dimensional strategy correction. Then derive the
late-window corollary from positive original Never, including its algebraic
retained-Never version, and implement the
absorbing-profile reward-Lipschitz bound before reselecting any source.
The named existing semantic declarations supply the complete-law adapter;
the determinant, gap estimate, generic selection, and source restriction
still require formalization.

## Exact finite certificate

This Python3/SymPy program reconstructs every matrix from its cap dynamics
and checks all216 determinants exactly. No floating-point or rank tolerance
is used, and no matrix payload is stored.

```python
from itertools import combinations, product
import sympy as s
G=s.Matrix([[0,-7,-3,-6],[5,0,-1,-3],[-6,6,0,7],[6,-7,-1,0]])
J=s.Matrix([[0,1,1,-2],[-2,0,6,-7],[-5,-5,0,-2],[1,-2,4,0]])
pairs=list(combinations(range(4),2)); determinants=[]
for word in product(pairs,repeat=3):
    z=s.eye(9)[:3,:]; rows=[]
    for k,pair in enumerate(word):
        q=s.zeros(4,9)
        for n,i in enumerate(pair): q[i,3+2*k+n]=1
        rows.append(z-J[1:4,:]*q)
        z=z-G[1:4,:]*q
    M=s.Matrix.vstack(*rows)
    d=M.det(); assert d!=0
    determinants.append(abs(d))
assert len(determinants)==216 and min(determinants)==12
print('PASS: all216 three-date pair-contact determinants are nonzero.')
```
