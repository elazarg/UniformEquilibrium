# Global absorbing partial-Nash minima have a strict pivot margin

Owner: CODEX_EXPENSIVE_EXIT.

Status: ordinary mathematical proof. Sections 1--8.1 passed independent
[CODEX_PIVOT_INDEPENDENT review](../feedback/CODEX_EXPENSIVE_EXIT__ABSORBING_PARTIAL_NASH_MINIMUM__BY_CODEX_PIVOT_INDEPENDENT.md).
This is a source reduction and transfer of existing finite-word consumers.
No Lean check, export, or solution of Fin4 is claimed.

Curation: references now point to retained proof sources, and Section 4
relocates its finite-root proof here. The review records its original scope;
this source relocation does not claim a new export review.

The new source minimizes the remaining pivot debt over the entire
absorbing partial-Nash carrier, without a low-cap constraint or a Never
penalty. Every such minimum has strictly positive pivot payoff. Combining
this with the existing zero-face and three-owner finite-word arguments
leaves only an all-positive source or a balanced three-zero joining cycle.
After a generic participant-pair perturbation, only the all-positive
source remains. Section 8 also checks the missing low-cap return for the
strict-cycle expanding ray. It removes an inert collapsed canonical
source generically, leaving the expensive positive-cap exit as the sole
canonical alternative. That exit is not consumed here.

This does not replace the [canonical low-cap minimum](../exports/UNIVERSAL_CANONICAL_PIVOT_EXIT_REDUCTION.md)
by a different source while retaining its old extremality. It constructs
and uses a separate global minimum. The positive inverse return is already
proved in Section 10 of that packet; its proof is not duplicated here.

## 1. Source and exact statement

There are four players I. Native rewards Z_i(S), for nonempty quitting
coalitions S, satisfy Z_i({i})=0. Live and Never payoff is zero. Prescribed
complete stopping laws are private and independent. A response replaces
one player's entire stopping law, including every finite date and Never.
Fix M>=1 bounding all absolute rewards.

Let K be the compact closure of actual ABSORBING prescribed payoff and
full-response-cap pairs (U,B). Write d_i=B_i-U_i and assume

    g=min_(X in K) max_i d_i(X)>0.

All debts are nonnegative. Fix any pivot p and put

    C_p={X in K: d_i(X)=0 for all i!=p},
    m_p=min_(X in C_p) d_p(X),
    M_p={X in C_p: d_p(X)=m_p}.

The sets C_p and M_p are nonempty compact sets and m_p>=g. EVERY X in M_p
satisfies, writing m=m_p,

    B_i=U_i>=0 for i!=p,
    B_p>m,                 U_p=B_p-m>0.                 (1)

Moreover AllContinue is the unique exact Nash root at continuation U.
Consequently the set T={i:U_i=0} has either zero or three elements. In the
three-zero case T=I minus {p}. Define on T

    G_ij=Z_i({j}),
    J_ij=Z_i({i,j})  for i!=j,
    L=J-G,

with all three diagonals zero. After cyclic relabeling of T,

    L_i,next(i)=a_i>0,       L_i,prev(i)=-b_i<0,
    product_i a_i=product_i b_i.                        (2)

Thus a nonsingular joining block cannot occur at a three-zero global
minimum. In particular, if det L_T!=0 for every three-player principal
joining block of the table, EVERY X in EVERY M_p has U_i>0 for all i.

The conclusion in (2) is necessary, not sufficient. This note supplies
neither a positive-gap game nor a consumer of all-positive M_p.

## 2. Nonempty carrier and prefix budget

Nonemptiness does not require the canonical low-cap theorem. Prescribe
p to quit surely at date zero. The three observers have a finite
Continue/Quit game at that date; take any mixed Nash equilibrium of that
three-player game. Since p quits surely, any observer's positive finite
deadline and Never have exactly the Continue payoff. Its entire response
menu therefore consists of the two finite-game endpoint values. The
profile absorbs surely and has d_i=0 for i!=p, so it belongs to C_p.
Compactness now gives M_p, and m_p>=g follows from the zero observer debts.

For a product root q, let c=product_i(1-q_i), H_i=product_(j!=i)(1-q_j),
Q_i its forced-Quit endpoint, and P_i its passive payoff on nonempty
opponent coalitions. The exact prefix formulas are

    U'_i=q_i Q_i+(1-q_i)(P_i+H_i U_i),
    B'_i=max(Q_i,P_i+H_i B_i),
    d'_i=c d_i+R_i(q;B),
    R_i=max(Q_i,C_i)-q_i Q_i-(1-q_i)C_i>=0,
    C_i=P_i+H_i B_i.                                    (3)

The cap maximum covers every complete response, without requiring that a
supremum be attained. Prefixing the same finite word to actual absorbing
approximants proves that every finite prefix preserves K.

Call q observer-Nash if its observer coordinates are best replies in the
finite root game at continuation B. Then R_i=0 for every observer, so a
prefix of a point in C_p remains in C_p. At X in M_p, (3) gives

    R_p(q;B)>=m(1-c).                                   (4)

For a>=0 take any exact four-player Nash root at B-a e_p. It is
observer-Nash at B and its pivot regret at B satisfies

    R_p(q;B)<=a q_p H_p.

For a mixed pivot this is equality; for pivot Continue it is zero; for
pivot Quit it follows from its shifted best-response inequality. Hence,
writing H=H_p,

    m(1-H)<=(a-m)q_p H.                                (5)

For 0<=a<m this forces q=0, equivalently c=1. Thus AllContinue is Nash
at B-a e_p. Letting a increase to m yields B_i>=0 for observers and
B_p>=m. These conclusions hold at EVERY global minimum.

## 3. Strictness of the pivot margin

Suppose a global minimum has B_p=m. For an observer i write

    Delta_ip=Z_i({i,p})-Z_i({p}).

First, B_i=0 implies Delta_ip<=0. To prove this, choose an exact root at
B-(m+eta)e_p with 0<eta<m. Equation (5) gives

    m(1-H)<=eta q_p H.

The pivot probability is positive: otherwise every observer continues,
and p would strictly prefer its own singleton zero to continuation -eta.
Every observer probability obeys

    q_j<=1-H<=(eta/m)q_p<1.                            (6)

If B_i=0 and Delta_ip=D>0, let j,k be the other observers. On their
joint Continue event the i Quit-minus-Continue gap is q_p D. On its
complement the absolute coalition-gap contribution is at most 2M. Thus

    gap_i>=q_p[D(1-2eta/m)-4M eta/m]>0

for sufficiently small eta. This contradicts q_i<1 and i's Nash
condition. Therefore

    B_i=0 implies Delta_ip<=0.                         (7)

Positive g also forces a negative entry in the singleton column p. Indeed,
if every Gamma_ip=Z_i({p}) for i!=p were nonnegative, let p use a constant
geometric hazard t>0 and let every observer Never. The profile absorbs.
Its pivot payoff and cap are zero. Observer i has payoff Gamma_ip and cap
max(Gamma_ip,t Z_i({i,p})), so all debts tend to zero with t. This would
contradict g>0.

Consider the diffuse solo-p prefix with total survival r. Its exact
limit, obtained by subdividing the one-owner hazard into vanishing
microhazards, is

    U_p^r=r U_p=0,       B_p^r=B_p=m,
    U_i^r=r B_i+(1-r)Gamma_ip,
    B_i^r=max(0,r B_i+(1-r)Gamma_ip)   for i!=p.         (8)

The formula is a limit of finite prefixes and so maps this source into
K. It follows directly from the scalar full-cap maximum in (3): each
immediate Quit endpoint tends uniformly to zero, while all later Continue
values lie between the affine endpoint and the original nonnegative cap.

If already some B_i=0 and Gamma_ip<0, keep the original minimum. Otherwise
every negative Gamma_ip has B_i>0. Decrease r from one to the first zero,

    r_*=max_(Gamma_ip<0) [-Gamma_ip/(B_i-Gamma_ip)] in (0,1).

For r in [r_*,1], every observer affine value in (8) is nonnegative;
thus all observer debts remain zero and d_p=m. Every resulting point is
again a GLOBAL minimum. At the endpoint some observer i has B_i=0 and
Gamma_ip<0. In either case we have such a global minimum.

Apply (7) to every zero observer at that endpoint. For sufficiently small
t>0, the literal root where p alone quits with probability t is
observer-Nash: its observer comparison is exactly

    t Delta_jp-(1-t)B_j<=0.

Zero observers satisfy this by (7), and the finitely many positive caps
allow a common small t. The pivot cap stays m and its prescribed payoff
stays zero. Hence the successor is again a global minimum. But for the
chosen observer i, Continue is optimal and

    B'_i=t Gamma_ip<0,

contradicting the nonnegative observer caps proved in Section 2. This
excludes B_p=m at EVERY global minimum and proves (1).

This differs from the older
[Never-penalized partial-Nash proof](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_PARTIAL_NASH_PREFIX_BARRIER.md):
there the critical face is excluded by minimizing a positive original
pivot Never mass. Here the carrier is absorbing and that argument is
unavailable. The diffuse first-zero endpoint followed by a literal root
supplies the contradiction instead.

## 4. Root inertia and the zero-face classification

At a=m, (5) forces H=1. Thus every exact root at B-m e_p=U has all
observers Continue. Its pivot continuation is U_p>0, so p also strictly
prefers Continue. This proves uniqueness of AllContinue.

Here is the finite-game argument, valid for arbitrary nonnegative
continuation U. It relocates the proof from Sections 6.1--6.3 of Git path
`b8d49627:math/exports/NATIVE_LEAST_NEVER_ZERO_PAYOFF_FACE_REDUCTION.md`.
Write Delta_i=Quit minus Continue, let T={i:U_i=0}, and let R>=1 bound
the absolute values of all rewards and U. Choose rho in (0,1/2] small
enough that every positive-continuation owner strictly Continues throughout
[0,rho]^I. This follows from

    |Delta_i(q)-Delta_i(0)|<=4R sum_(j!=i) q_j.

When those outsiders Continue, writing z=sum_(i in T)q_i gives

    |Delta_i(q)-sum_(j in T)L_ij q_j|<=4R z^2.

For 0<epsilon<1 restrict each zero owner to the two actions
Bernoulli(epsilon) and pure Quit, leaving outsiders unrestricted.
Finite-game Nash produces q^epsilon with q_i>=epsilon on T.
Its unrestricted regret is at most 2R epsilon: its value F satisfies
F>=Q and F>=epsilon Q+(1-epsilon)C, so C-F<=2R epsilon.
A sequence of these constrained equilibria outside [0,rho]^I with
epsilon decreasing to zero therefore has a nonzero exact unrestricted
cluster root. Inside the cube, outsiders Continue and Delta_i>0 forces
q_i=1, which is impossible.

A singleton T permits a small indifferent solo root. With two zeros,
a nonpositive reciprocal coefficient likewise permits a solo root.
If both reciprocal coefficients are positive, the exact comparisons
Delta_i=L_ij q_j and Delta_j=L_ji q_i force both constrained owners
to Quit surely inside the cube, impossible. Thus one or two zeros always
produce a nonzero exact root.

If a probability row w satisfies w^T L>=kappa 1 for kappa>0,
decrease rho so 4R |T|rho<=kappa/2. Inside the cube,

    sum_i w_i Delta_i>=kappa z-4R z^2>0.

Some constrained owner then strictly prefers Quit, again impossible.
Hence the same cluster argument gives a nonzero exact root. Finally,
a column of L with no positive entry permits a small solo root in that
column. Since the present continuation has only the AllContinue root,
T cannot have one or two elements, every column has a positive entry,
and no such positive multiplier exists. Finite minimax therefore supplies
a probability column v with Lv<=0 whenever T is nonempty.

If there are three zeros, this v has full support. Support one contradicts
a positive column. On support two, the two reciprocal coefficients are
nonpositive, so their positive column entries both lie in the third row,
contradicting Lv<=0 there. Each row can have at most one positive entry;
the three positive columns therefore use exactly three positive entries,
forming a cycle. The remaining entry in each row is strictly negative.
Multiplication of the row inequalities gives

    L_i,next(i)=a_i>0,       L_i,prev(i)=-b_i<0,
    product a_i<=product b_i.                           (9)

The pivot is positive by (1), so these exhaust the possibilities for T.

## 5. Transfer of the existing whole-pencil consumers

The following elementary transfer is the reason the old diagonal
three-zero proofs apply to this new source. Suppose U_T=B_T=0, B_p=b>0,
and d_p=m>0. Consider finite words using only observer roots. Suppose
their total hazard sums are at most b/(16M), their common survival is at
most theta<1, and a virtual observer comparison has terminal seam tending
to zero and endpoint observer debts tending to zero. The latter debts
may already be zero; no actual realization of the virtual seam is needed.

Keep the pivot's ACTUAL nondiagonal pair (U_p,b) at the virtual terminal
seam. At a root of total observer hazard ell, its immediate Quit endpoint
has absolute value at most M ell. Its Continue cap differs from its
previous cap by at most 2M ell. Inductively the Continue cap stays at
least 7b/8 while the Quit endpoint is at most b/16. Thus the pivot
strictly Continues at every root, and its debt is exactly c m at the
end of the word. The coordinatewise prefix formulas are one-Lipschitz
in their own continuation payoff and cap, so attaching the SAME finite
word to the actual point gives observer debts tending to zero. Compactness
produces a point in C_p with pivot debt at most theta m<m, a contradiction.

This transfer requires only bounded total hazard, vanishing full-cap
seam error, and a fixed survival drop. It does not require observer debts
to be zero at a finite mesh. All its approximating endpoints remain in K.

We now check these requirements for the finite-word constructions in
Proof Sections 11, 13 and 14 of
[the canonical pivot packet](../exports/UNIVERSAL_CANONICAL_PIVOT_EXIT_REDUCTION.md).
The transfer above supplies the C_p contradiction; no F_p extremality is
being assigned to the present source.

* If G has a nonzero homogeneous complementary vector v, normalized by
  sum v_i=1, prepend floor(t/epsilon) copies of q=epsilon v. Fix t>0
  sufficiently small. Proof Section 11 bounds the observer debts by
  O(M(1+t)epsilon), total hazard by t, and common survival tends to
  exp(-t)<1. Its proof uses only the zero observer tail and full-cap
  recursion, so it is unchanged. The transfer proves that G is R0.
* If some column of G-sJ is nonnegative for a fixed 0<s<1, the singleton
  burst in Proof Section 13 uses r_n=f(1-s)^n/(1-f+f(1-s)^n) and hazards
  q_n=s r_n in that column's owner. Its virtual observer pair is
  G_ij r_n, with the mover coordinate zero. The observer roots are exact
  because G_ij-sJ_ij>=0. The terminal seam tends to zero, the total
  hazard is at most f/(1-f), and survival is at most 1-sf<1. Choose f
  small enough for the pivot cap buffer. Such a column is impossible.
* If L is invertible and L^(-1)J has a positive eigenvector with real
  eigenvalue rho>1, the backward-orbit construction in Proof Section 14
  gives positive roots
  q_n=a rho^n v+O(a^2 sigma^n), n<=0, with rho<sigma<rho^2. Their
  virtual continuation is c_i(q)=(Q_i(q)-P_i(q))/H_i(q); the recurrence
  c(q_(n+1))=Q(q_n) makes every observer root exact. The seam at q_-n
  tends to zero, total hazard is at most C a, and survival is at most
  exp(-c_0 a)<1. Choose fixed a small enough for the pivot buffer. The
  recurrence proof needs no eigenvalue dominance or simplicity. Again
  the transfer gives a contradiction.

These are constructive finite-word proofs, not an invocation of the old
least-Never conclusion at a nondiagonal point.

Suppose the inequality in (9) were strict. Then L is invertible and -L
is R0 with strictly positive inverse and R0 degree one, by the explicit
three-by-three cofactor and degree calculations in Proof Sections 12 and 15
of the canonical pivot packet. The three transferred
consumers prove that every matrix G-sJ, 0<=s<=1, is R0. Indeed, a
homogeneous complementary vector can have support one, two, or three.
Support one is the forbidden nonnegative column. On support two the two
active reciprocal entries vanish; the one remaining row has a nonnegative
weighted sum, so at least one of those two columns is itself nonnegative.
On support three, (G-sJ)x=0 with x>>0 gives
L^(-1)Jx=x/(1-s), the forbidden expanding eigenvector. Endpoints are
covered by G R0 and -L R0.

For completeness the remaining finite-dimensional implication is exact.
The homogeneous minimum maps x -> min(x,(G-sJ)x) have no nonzero zero.
Compactness of the parameter interval and unit sphere gives a common
degree domain, so every pencil matrix has degree one. The bounded-offset
homotopy then makes every pencil matrix standard Q. Choosing LCP offset
-one shows that every row has a positive entry; R0 shows that every
column has a negative entry. In a zero-diagonal three-by-three matrix
these six requirements use all six off-diagonal positions. Every row and
column has one entry of each sign, none is zero, and the signs cannot
change along the pencil. The Q witness x satisfies Gx>=one. Multiplying
the resulting three strict cycle inequalities gives positive determinant;
the three-by-three inverse formula consequently gives G^(-1)>>0.

The positive-inverse pivot-debt return in Proof Section 10 of
[the canonical pivot packet](../exports/UNIVERSAL_CANONICAL_PIVOT_EXIT_REDUCTION.md)
then supplies a point in C_p with strictly smaller pivot debt. Its
hypotheses hold because B_T=U_T=0 and b=B_p>0. This is the final
contradiction. Hence equality must hold in (9), proving (2).

## 6. Generic all-positive frontier and its limitation

For each triple T, det L_T is a nonzero polynomial in the participant
pair rewards. Its nonzeroness is immediate, for example by prescribing
one directed cycle of joining differences equal to one and its reverse
cycle equal to zero. The product of the four triple determinant
polynomials is therefore nonzero. Its nonvanishing locus is open dense
in the native reward space, even when singleton and all non-pair rewards
are fixed.

Changing every reward by at most epsilon changes every prescribed payoff
and every complete response payoff by at most epsilon. Full caps change
by at most epsilon uniformly over all laws, so each debt changes by at
most 2epsilon. Thus g changes by at most 2epsilon. Any native table with
g>0 admits arbitrarily small participant-pair perturbations retaining
positive g and making all four joining determinants nonzero.

For each such perturbed table, each pivot has a nonempty global minimizing
set M_p, and EVERY point of EVERY M_p has all four payoffs strictly
positive. Compactness gives a positive payoff margin on their finite
union. This removes the all-zero alternative that remains in the old
least-Never global selection. It does not prove that an all-positive
source is impossible, or that the original unperturbed sources satisfy
the same positive margin.

There is also an exact separation from the canonical low-cap minimum.
Let F_p={X in C_p:min_i B_i<=0}. Its nonemptiness is supplied by the
separate canonical low-cap producer linked above; the finite observer
Nash construction in Section 2 does not assert a low pivot cap. Under
the determinant condition, M_p and F_p are disjoint compact sets. Consequently

    min_(X in F_p) d_p(X)>m_p.

Thus a return to the low-cap chamber cannot be justified merely by
globally minimizing the remaining debt. The positive-cap plateau is a
real missing consumer in this argument.

## 7. Checks, overlap, and next question

The zero-face classification and all three finite-word producers are
existing mathematics; their new use here is the absorbing partial-Nash
minimum with a nondiagonal pivot. The strict pivot margin is a new
absorbing replacement for the positive-Never selector argument. The
positive inverse return is independently recorded in the linked owned
note and is not claimed again as a separate new theorem.

The same bounded observer words also contract the old objective
d_p+r nu: while the pivot Continues, both summands multiply by the common
survival. Therefore generic all-positive partial-Nash existence without
specifying its carrier is not itself the increment here. The new source
content is minimization on the ABSORBING carrier with no Never penalty,
the strict payoff margin there, and its separation from F_p. The
low-cap return sign in Section 8 has a separate role and uses the
canonical F_p extremality directly.

The literal formulas were inspected in `quittingTerminalDeviationDebt`,
`quittingRootSuccessorPayoff_eq_max_of_isZeroNash`, and
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`, and in
`quittingTerminalSemanticPair_rootThenContinuation` and
`continuous_quittingTerminalSemanticPrefix` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
No Lean command was run.

The concrete next question is whether an all-positive global M_p source
admits an actual incoming decomposition or a full replacement that lowers
d_p while preserving all three observer debts. Its finite-prefix identity
alone does not do so: an incoming tail may have pivot debt larger than m_p.
Positive observer debt cannot be repaired exactly by a finite nonsure
prefix, because (3) only multiplies it by c and adds nonnegative regret.

## 8. A strict-cycle expanding ray also returns to the low-cap carrier

The transfer in Section 5 used GLOBAL C_p minimality. It must not be
applied unchanged to a minimum on the smaller low-cap set F_p: an
expanding-ray word for a general invertible L could end with every cap
positive. The strict joining-cycle case has an additional sign that
repairs precisely this issue.

Suppose X minimizes d_p on F_p, with

    U_T=B_T=0,       B_p=b>0,       d_p=d>0,

and AllContinue is the only exact root at continuation B. The zero-face
root classification applies to B, since its pivot coordinate is strictly
positive. It gives the joining cycle (9). Assume its product inequality
is strict. Then (-L)^(-1)>>0, as verified in Section 5.

Consider a full-support homogeneous direction of G-sJ for 0<s<1.
It yields v>>0 with

    L^(-1)Jv=rho v,       rho=1/(1-s)>1.

There is an index i with (Lv)_i<0. Otherwise Lv>=0 and
v=L^(-1)Lv<=0, since L^(-1)=-(-L)^(-1) is entrywise strictly negative.
This contradicts v>>0. Fix such an i and write kappa=-(Lv)_i>0.

The backward-orbit producer in Appendix A.4 of the strict three-zero
packet has q_0=a v+O(a^2). Its forced-Quit output satisfies

    Q(q_0)=a Jv+O(a^2)=a rho Lv+O(a^2).

Choose a>0 small enough that the ith remainder has magnitude at most
a rho kappa/2, as well as satisfying all orbit and pivot-buffer bounds.
At the END of each virtual finite word q_-n,...,q_0, the observer payoff
AND cap are Q(q_0), because the last construction root q_0 is exactly
mixed at continuation c(q_0). Thus

    virtual B_i(end)<=-a rho kappa/2<0.                 (10)

The actual terminal seam c(q_-n) tends to zero. Coordinatewise full-cap
nonexpansivity consequently transfers (10) to the compact actual limit.
The observer debts vanish, the pivot debt is c d<=theta d<d, and the
limit has a strictly negative observer cap. It lies in F_p and contradicts
its minimum. No approximation is required in the sign of the limit.

The other two whole-pencil producers also return to F_p: the repeated
homogeneous singleton direction leaves each active observer at payoff/cap
zero in the limit, while the singleton burst leaves its sole mover at
zero. Therefore the entire strict-cycle pencil argument of Section 5
now applies to this low-cap minimum. It produces G^(-1)>>0, which the
positive-inverse return excludes. We have proved:

    At a collapsed F_p minimum with B_p>0 and an inert root game at B,
    the three-observer joining block must satisfy det L=0.             (11)

The negativity in (10) is essential. There is no claim that arbitrary
expanding supported-root words return to a low-cap face.

### 8.1. Generic unification of the canonical alternatives

The canonical producer gives, for each pivot, an F_p minimum with either
an already nonzero exact cap-Nash exit or collapsed shape

    B=b e_p,       U=(b-d)e_p,       b>=d>=g>0.

If the collapsed source has any nonzero exact root at B, use that root
instead of requiring the prelimit selected roots themselves to have a
nonzero limit. Its successor has debts c d e_p by (3). The survival c
cannot be zero, because that would give a zero-debt point in K. It is
strictly below one. If the successor had min B<=0, it would lie in F_p
with smaller pivot debt, another contradiction. Hence every coordinate
of its successor cap W is strictly positive.

If the collapsed source has no nonzero root at B, (11) forces det L=0.
Consequently, when all four principal joining determinants are nonzero,
EVERY chosen canonical source admits a nonzero nonsure exact cap-Nash
root whose successor has all caps positive and only pivot debt c d.
The canonical first-zero pivot return still yields its expensive-return
inequality

    r c d+(1-r)W_p>=d,
    W_p>d,

where r is the first-zero survival for the negative singleton column p.

The generic perturbation in Section 6 preserves positive g and supplies
the determinant condition. Thus the collapsed alternative can be
discarded for the purpose of a generic positive-gap contradiction. The
remaining task is a complete consumer of the expensive positive-cap
exit. This conclusion does not assert such a consumer or solve Fin4.
