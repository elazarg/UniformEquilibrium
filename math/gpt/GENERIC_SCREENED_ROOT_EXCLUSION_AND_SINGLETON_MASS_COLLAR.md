# Generic screened-root exclusion and a singleton-mass collar

Date: 2026-09-09.

Status: ordinary mathematical proofs developed in this response. Not independently
reviewed or Lean-checked. No repository source, branch, commit, or PR was changed.
The companion script checks exact finite algebra, not the conjecture or the
universal claims by sampling.

## 1. The result

There are four players. Every nonempty quitting coalition S pays r(S) in R^4;
live play and Never pay zero. Strategies and deviations are unrestricted
behavioral strategies with independent private randomization. Equivalently,
players independently choose clocks in N union {Never}.

For an actual profile p, write U_i(p) for its terminal payoff, B_i(p) for its
supremum over ALL unilateral replacement laws, d_i=B_i-U_i, and

    E_r(p)=max_i d_i(p),       eta(r)=inf_p E_r(p).

All terminal rewards are normalized into [-1,1] by a common positive scaling.
Write s_i=r_i({i}), and let b denote the other 56 reward coordinates. Thus
r_b(s), s in [-1,1]^4, is the entire own-singleton fiber over b.

A screened root is a date-zero independent product root with at least two
sure quitters, followed by Never. Let

    theta(b)=min { E_{r_b(s)}(q) : q is a screened root },
    Omega_b=max_{s in [-1,1]^4} eta(r_b(s)).

The first expression does not depend on s. Both extrema are attained.

**Theorem A: an explicit generic exclusion.** There is a nonzero homogeneous
integer-coefficient polynomial Pi in b, of degree 144, with these properties:

1. Pi is the product of 24 explicit degree-six expressions, each computed
   from a 3-by-4 matrix of bilinear regret coefficients.
2. If Pi(b) is nonzero, no screened root has four equal strictly positive
   COMPLETE debts, for any choice of the four own singletons.
3. Consequently, if Pi(b) is nonzero and Omega_b>0, then

       theta(b)>Omega_b.                                 (A)

This is a strict gap for ALL screened roots, including mixed two-sure and
three-sure roots, not only pure sure coalitions.

**Theorem B: counterexample-preserving fiber selection.** If any four-player
counterexample exists, one can choose

    b in Q^56 intersect (-1,1)^56,       Pi(b) != 0,
    Omega_b>0,                         gamma>0,

such that, for EVERY s in [-1,1]^4 and EVERY screened root q,

    E_{r_b(s)}(q) >= Omega_b+gamma.                        (B)

Gamma can be taken rational. Thus this is an existential reduction of a
hypothetical counterexample, not an assumption that arbitrary input data
already satisfy the determinant test.

**Theorem C: a prescribed-singleton mass collar.** At any fixed table with
Pi(b) nonzero and eta(r)>0, every maximum-debt minimizing point of the joint
semantic/outcome-law carrier has strictly positive TOTAL singleton mass.
Moreover, there exist kappa>0 and epsilon_0>0 such that EVERY actual profile p
satisfies

    E_r(p) <= eta(r)+epsilon_0
        ==> sum_i Pr_p(first coalition={i}) >= kappa.     (C)

There is also a fiber-uniform version: for every a>0, the same kappa and
epsilon_0 can be chosen for all s with eta(r_b(s))>=a, provided that set is
nonempty.

The source obtained by maximizing eta over the selected fiber therefore
retains a positive singleton mass on EVERY sufficiently accurate actual
approximant. The common-calendar source in the uploaded membership-fiber
packet can be selected with this additional field, without changing its
profiles, its labels, or its weights.

**An additional full-prefix consequence.** At every positive global minimum
m of maximum debt, put L_i=B_i-s_i. Then

    sum_i m/L_i <= 1.                                    (H)

For four-player reward tables in [-1,1], this implies eta(r)<1/3. In
particular, the maximum of eta over the entire unit reward cube is strictly
below 1/3. This is a gap bound, not vanishing exploitability.

The contribution is a stronger counterexample-source reduction. It eliminates
zero-singleton minimum laws after an allowed table perturbation and removes
the whole screened-root branch, including opposed three-sure reversals and
the two-sure case. It does NOT construct arbitrarily low-regret profiles or
consume the remaining positive-singleton source.

## 2. Complete response semantics and the two existing minimum lemmas

Let K_r be the closure of the actual pairs (U(p),B(p)). Its coordinates are
bounded, so K_r is compact. All debts are nonnegative on K_r. The continuous
maximum-debt functional has minimum eta(r) there.

Prefix a product root q to a supplied actual profile, or apply its continuous
prefix map to a carrier pair. Define

    c=prod_i(1-q_i),       a=1-c,
    beta_i=prod_{j!=i}(1-q_j),       pi_i=q_i beta_i,

and let Q_i be player i's Quit-now reward and H_i its absorbing contribution
from opponents quitting while i Continues. The EXACT full-cap equations are

    U'_i=q_i Q_i+(1-q_i)(H_i+beta_i U_i),
    B'_i=max(Q_i,H_i+beta_i B_i).                         (1)

For the second equation, Continue permits every old replacement law after
survival, so its supremum is H_i+beta_i B_i. This remains true without cap
attainment and when beta_i=0. A random choice between the two first actions
cannot exceed their maximum. The map in (1) is continuous and preserves K_r.

Here are short proofs of the already available minimum facts. They also
specify exactly what the new argument consumes.

### 2.1 Singleton-cap moat at a MAXIMUM-debt minimum

Let (U,B) minimize maximum debt at m>0. For 0<=h<m, choose an exact finite-game
Nash root against the continuation annotation v=B-h*1. Let w_i be its root
payoff. Finite-game Nash existence is sufficient; v need not be a behavioral
payoff.

Nash optimality gives B'_i<=w_i+beta_i h, while
U'_i=w_i+c(h-d_i). Hence

    d'_i<=c d_i+pi_i h<=c m+a h=m-a(m-h).                (2)

If a>0, every full debt is strictly below m, contradicting the carrier minimum.
Therefore this root is all Continue. Its Nash inequalities imply B_i-h>=s_i.
Let h increase to m to obtain

    L_i=B_i-s_i>=m,       U_i>=s_i.                       (3)

These are inequalities at the SAME maximum-debt minimum. No total-debt minimum
is substituted.

### 2.2 All players tie

Suppose d_k<m. Prefix a solo-k hazard h>0, with all other players Continue.
Equation (3) gives B_k>s_k, and (1) gives

    d'_k=d_k+h(U_k-s_k),
    d'_j=max((1-h)(s_j-U_j)
                     +h[r_j({k,j})-r_j({k})],
             (1-h)d_j),                    j!=k.         (4)

Using |r|,|U|<=1 and U_j>=s_j, choose

    0<h<min(1, m/2, (m-d_k)/2).

The owner debt, the initial joining branch of every other cap, and every
continued old debt are then all strictly below m. This contradicts minimality.
Thus

    d_i=m for all four players.                         (5)

Both lemmas are already represented in the inspected repository; their proofs
above are included for semantic completeness, not claimed as new results.
They hold on the carrier, even when its minimizing pair has no actual
realization.

## 3. Four exact bilinear debt branches at a screened root

Fix a sure pair K={a,b}; order the other players c,d. Their independent
Quit0 probabilities are x,y in [0,1]. The sure players' probabilities are one.
All prescribed laws use only date zero and Never.

After ANY one player deviates, at least one of the original sure players
still quits at zero. Hence that deviation's complete payoff depends only on
whether it quits at zero or Continues. Every later finite date and Never
has the Continue value. This is a full-cap screening statement, not a
restriction of the deviation menu.

Let T be the independent optional quitting set, with c present with probability
x and d present with probability y. Define

    G_a(x,y)=E[r_a((K\{a}) union T)-r_a(K union T)],
    G_b(x,y)=E[r_b((K\{b}) union T)-r_b(K union T)].

The sure players' actual debts are max(0,G_a) and max(0,G_b).

Define the optional players' Quit-minus-Continue gaps

    Delta_c(y)=E_d[r_c(K union {c} union T_d)-r_c(K union T_d)],
    Delta_d(x)=E_c[r_d(K union {d} union T_c)-r_d(K union T_c)].

Their actual debts are

    d_c=max((1-x)Delta_c(y), -x Delta_c(y)),
    d_d=max((1-y)Delta_d(x), -y Delta_d(x)).               (6)

For each optional player select one of the two labels Q,C and put

    F_c^Q=(1-x)Delta_c(y),       F_c^C=-x Delta_c(y),
    F_d^Q=(1-y)Delta_d(x),       F_d^C=-y Delta_d(x).

There are four label pairs sigma=(sigma_c,sigma_d). For each one, the four
formal debt branches

    F_a=G_a, F_b=G_b, F_c=F_c^sigma_c, F_d=F_d^sigma_d   (7)

are bilinear functions of x,y. A formal branch need not be a nonnegative debt
outside its appropriate best-action region. This causes no problem: if all
ACTUAL debts equal some m>0, G_a=G_b=m and one label pair makes all four
functions in (7) equal m. The argument uses a finite union over ALL label
pairs, not a fixed sign assumption.

The boundaries x=0,1 and y=0,1 are included. Three-sure and four-sure roots
therefore require no additional polynomials or limiting argument.

Every reward entry in these expressions is among b. When a sure player
Continues and only the other sure player quits, the resulting singleton is
not its OWN singleton. Every optional endpoint retains the original sure pair.
Thus none of the four own-singleton coordinates occurs in (7).

## 4. The explicit degree-six test

Use the monomial vector

    z(x,y)=(1,x,y,xy)^T,       z_0 z_3-z_1 z_2=0.         (8)

Write F_i=l_i z, with l_i a row of four coefficients. Form

    A_{K,sigma}=[l_b-l_a; l_c-l_a; l_d-l_a].              (9)

This is a 3-by-4 matrix whose entries are integer linear combinations of b.
To compute a bilinear coefficient row from corner values f00,f10,f01,f11, use

    l=(f00, f10-f00, f01-f00, f11-f10-f01+f00).

Let A_hat_j delete column j, and set

    w_j=(-1)^j det(A_hat_j),       j=0,1,2,3,
    P_{K,sigma}=w_0 w_3-w_1 w_2.                        (10)

Laplace expansion gives A w=0. If P_{K,sigma} is nonzero, w is nonzero,
rank A=3, and its kernel is exactly the line spanned by w.

Suppose the four branches in (7) were equal at some x,y. Then A z(x,y)=0.
Since z_0=1, z=t w for some nonzero t. Equation (8) would give

    0=t^2 P_{K,sigma},

a contradiction. This proves that a nonzero expression in (10) excludes that
branch's equalities even over complex x,y. No assumption about strict
complementarity, invertibility of a selected 3-by-3 minor, or avoidance of
probability endpoints is needed. If rank A<3, all cofactors and P vanish;
the test simply does not certify exclusion in that case.

There are six sure pairs and four label pairs. Define

    Pi(b)=product_{|K|=2} product_{sigma in {Q,C}^2} P_{K,sigma}(b).  (11)

Each factor is homogeneous of degree six. Thus a nonzero Pi is homogeneous
of degree 144 and proves Theorem A(2).

### 4.1 Every factor is a genuinely nonzero polynomial

Fix K and sigma. Independently in each recipient's reward coordinates, install
membership gaps making the four branches

    F_a=1/4,
    F_b=1/2+xy/4,
    F_c=L_sigma_c(x)/4,
    F_d=L_sigma_d(y)/4,                                 (12)

where L_Q(t)=1-t and L_C(t)=t.

For a core recipient, prescribe its four Continue-minus-Quit endpoint gaps
to be the four corner values in (12). For each such gap g, assign the Continue
reward g/2 and the Quit reward -g/2. The four pairs are disjoint and are all
among that recipient's non-own-singleton coordinates.

For an optional recipient, use the constant Quit-minus-Continue gap +1/4
for label Q or -1/4 for label C, at both configurations of the other optional
player. Assign those endpoint rewards as plus/minus half the gap. Recipient
blocks are disjoint, so these assignments never conflict. All rewards have
absolute value at most 3/8. Unspecified entries, including all own singletons,
can be zero.

After multiplying the three equality rows by four, their kernel is spanned by

    (1,xi,upsilon,-1),

where xi=0 for label Q and xi=1 for label C, and likewise for upsilon.
The quadratic expression in (8) on this vector is -1-xi*upsilon, never zero.
More explicitly, P=-1/2048 for sigma=(C,C) and P=-1/4096 for each other sigma.
Thus each factor is a nonzero polynomial. The real polynomial ring is an
integral domain, so their product Pi is also nonzero.

Consequently the set Pi!=0 is open and dense in R^56, and its complement has
empty interior. This uses only the elementary fact that a nonzero polynomial
cannot vanish on a nonempty open box, proved by successive univariate
specialization. Rational points with Pi!=0 are dense as well: every open set
meets the open nonvanishing set, which contains rational points.

This proof of density is analytic/algebraic. It does not infer genericity from
a random computation.

## 5. The strict gap on the entire singleton fiber

For fixed b, the set of screened roots is the union of six compact squares.
Equations (6) and the core positive parts make E a continuous function on that
set. It is independent of s. Hence theta(b) is attained.

Reward distance delta changes any prescribed or deviated terminal payoff by
at most delta, with the SAME outcome law. Taking suprema over all deviations
and then the maximum over players gives

    |E_r(p)-E_{r'}(p)|<=2 delta,
    |eta(r)-eta(r')|<=2 delta.                           (13)

Thus eta is continuous on the compact singleton fiber, and Omega_b is attained
at some s_*.

Assume Pi(b)!=0 and Omega_b>0. Every screened root is an actual profile, so
Omega_b<=theta(b). If equality held, a minimizing screened root would be an
actual global maximum-debt minimizer for r_b(s_*), of positive value Omega_b.
The all-player tie lemma (5) would make all its debts equal and positive,
contradicting (11). Therefore theta(b)>Omega_b.

Choose 0<gamma<=theta(b)-Omega_b, rational if desired. The gap is independent
of every own-singleton coordinate and holds over every screened product root.
In particular it implies the older strict floor for the eleven nonsingleton
pure sure coalitions, since those are a subset of these roots.

### 5.1 Counterexample-preserving selection

Start from any reward table with eta>0. Normalize by a common positive scale
so every reward lies strictly inside the unit cube. Equation (13) shows that
eta remains positive on a sufficiently small open reward neighborhood.

Perturb its 56 b coordinates, as slightly as necessary, to rational entries
inside (-1,1) with Pi(b)!=0. Keep its own singletons for now. The same
continuity bound preserves eta>0, so Omega_b>0. Section 5 then supplies the
strict screened-root gap for the whole fiber. This proves Theorem B.

The initial table can additionally be made rational in ALL its coordinates,
because positivity of eta is open. However the singleton value s_* maximizing
eta over a rational b fiber is not asserted to be rational.

Unlike the earlier membership-stretch reduction, this proof does not require
choosing a maximizer over all sixty reward coordinates, computing a signed
membership stretch, or preserving an old-table/final-table inverse-stretch
identity. It replaces that ancestry with generic b selection and singleton-only
maximization. An argument that still requires the exact old common-stretch
identity cannot treat it as a retained field of this new source.

## 6. Eliminating every zero-singleton minimum law

Let L_r be the closure of the actual triples (U(p),B(p),mu_p), where mu_p is the
probability vector on the fifteen nonempty first coalitions and Never. This
is a compact subset of a finite-dimensional box times a probability simplex.
Projection to (U,B) is K_r: one inclusion is immediate, and compactness of the
probability simplex supplies a convergent law subsequence for the reverse
inclusion. The prescribed-payoff identity

    U_i=sum_{S nonempty} mu(S)r_i(S)                     (14)

holds throughout L_r by continuity.

Fix a maximum-debt minimum (U,B,mu) in L_r with m=eta(r)>0, and suppose its
TOTAL singleton mass is zero. Each individual singleton mass is then zero.
We first show that mu(Never)=0; it is important not to assume this.

Take one sequence of actual profiles converging jointly to this triple.
Let a_{n,i} be player i's marginal Never probability and
p_n=product_i a_{n,i} the actual joint Never probability. Let u_{n,i} be its
prescribed singleton-i probability. Independence gives

    u_{n,i} >= (1-a_{n,i}) product_{j!=i} a_{n,j}
             >= p_n(1-a_{n,i}).                        (15)

The first term counts the event that only i EVER quits, which is certainly a
singleton-i first coalition. If mu(Never)>0, then p_n is bounded away from zero.
Since every u_{n,i} tends to zero, (15) forces all a_{n,i} to tend to one.
Hence mu(Never)=1.

But then U=0 by (14). The minimum moat U_i>=s_i forces every s_i<=0. All Never
is now an actual zero-debt profile, contradicting m>0. Thus mu(Never)=0.

All conditions of the existing exact product-base realization theorem now
hold: the triple belongs to the joint carrier, Never and every singleton
have zero mass, and B_i>s_i follows from B_i-s_i>=m>0. That theorem gives one
UNPADDED screened root realizing the SAME full pair (U,B) and the SAME law mu.
It has four equal positive debts by (5), contradicting Pi(b)!=0.

Equivalently, on the selected fiber one can use its strict screened-root gap:
the reconstructed profile would have E=m<=Omega_b<theta(b).

This proves positive total singleton mass at every such minimum. No limit
strategy was substituted for the joint carrier point. The only full-pair
realization occurs under the exact named product-base theorem's hypotheses.

## 7. The uniform near-minimum collar

For a fixed table, the subset of L_r where E=eta(r)>0 is nonempty and compact.
The continuous nonnegative function

    S(mu)=sum_i mu({i})

is strictly positive there by Section 6. Therefore it has a positive minimum
kappa_*>0.

If no epsilon_0>0 forced S(mu_p)>=kappa_*/2 on actual profiles with
E(p)<=eta(r)+epsilon_0, choose a sequence with E(p_n)<=eta(r)+1/n and
S(mu_{p_n})<kappa_*/2. Compactness gives a joint carrier limit at minimum debt
with singleton mass at most kappa_*/2, a contradiction. Set kappa=kappa_*/2.
This proves (C).

### 7.1 Uniformity across positive-gap portions of the fiber

Fix a>0. Consider all s with eta(r_b(s))>=a and all their minimizing joint
carrier points. This set is compact. The only extra fact needed is that the
joint carrier graph is closed as rewards vary.

To prove it, let r_n tend to r and let z_n in L_{r_n} tend to z. For each n
choose an actual profile approximating z_n within 1/n. Evaluate the SAME laws
at r. By (13), prescribed payoff and full caps change by quantities tending
to zero; the outcome law is unchanged. These actual triples converge to z,
so z belongs to L_r. The graph is therefore closed. Continuity of eta makes
the minimum condition and the lower gap threshold closed as well.

Section 6 gives S>0 everywhere in this compact set. Repeating the minimum
and near-minimum compactness argument proves the claimed uniform kappa and
epsilon_0 for all these tables simultaneously.

The threshold a>0 is necessary in this uniform statement: it does not provide
one positive singleton-mass lower bound as the game gap tends to zero.

### 7.2 Attachment to the actual common-calendar source

The common-calendar construction in Sections 4-6 of the uploaded
MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION depends, after its
initial table selection, on a fixed fiber b, a positive maximizing value
Omega_b, the pure sure-coalition margin, and the existing reward-uniform
finite approximation and singleton moat. The selected fiber above supplies
these hypotheses with the stronger screened-root margin (B).

Its selected tables have eta tending to Omega_b, and its actual finite inner
minimizers have full exploitability tending to eta. Apply Section 7.1 with,
for example, a=Omega_b/2. Every sufficiently late source profile, before or
after the silent shift, has total prescribed singleton mass at least kappa.
Silent shifting preserves that law. Discarding calendars, choosing a tuple
entry, and retaining or transporting its tester weights do not change this
uniform fact.

Thus the original same-profile/same-weight activity, directional stationarity,
all-owner weight, and total singleton-pressure conclusions can coexist with

    sum_i mu_p({i}) >= kappa.                            (16)

By finiteness, an infinite subsequence has one fixed owner i with
mu_p({i})>=kappa/4. This is a bound on its TOTAL first-coalition singleton
probability. It is NOT a bound at one fixed date, a response-singleton mass,
an assertion of cap attainment, or a claim that an actual profile realizes
a minimizing carrier pair.

In particular the new field does not repair the missing post-response debt
control. It changes the available source, not the temporal interpretation of
a response arrow.

## 8. An additional harmonic constraint and the strict one-third bound

This calculation is independent of genericity. It applies to every positive
maximum-debt minimum of every unit-bounded finite-player game. Continue to
write d_i=m and L_i=B_i-s_i>=m.

For positive rates lambda_i and a small t>0, prefix ONE independent product
root with q_i=t lambda_i. Because B_i>s_i at t=0, all complete-cap branches
remain Continue for sufficiently small t, by continuity of the finitely many
endpoint gaps. Equation (1) then has the first-order expansion

    d'_i=m+t[lambda_i(U_i-s_i)-m sum_{j!=i}lambda_j]+O(t^2)
        =m+t[lambda_i L_i-m sum_j lambda_j]+O(t^2).       (17)

Each prescribed or deviating outcome is included in (1); the collision terms
enter the remainder, not an omitted response class. Finiteness makes one
small-t interval work for all coordinates.

Set lambda_i=1/L_i. If m sum_i 1/L_i>1, every first derivative in (17) is the
same strictly negative number, so all debts fall below m for sufficiently
small t. This is an actual prefix or its continuous carrier image and
contradicts minimality. Hence (H) holds.

For n>=2, every L_i>m follows immediately: otherwise the i-th summand in (H)
would be at least one, and every other summand is strictly positive. Thus
U_i>s_i at EVERY positive maximum-debt minimum. More quantitatively, since
L_j<=2 in the unit normalization,

    L_i >= m/[1-(n-1)m/2],
    U_i-s_i >= (n-1)m^2/[2-(n-1)m],                    (18)

with positive denominators; their positivity follows from (H) itself.
These are MAXIMUM-debt minimum statements, distinct from the uploaded
quadratic collar for minimum TOTAL debt.

Now specialize to four players. Let a=max_i s_i. All Never has exploitability
max(0,a). It must be strictly greater than m: equality would make all Never a
positive minimum, while the moat fails for an owner attaining its positive
singleton cap there. Hence

    0<m<a<=1.

Choose k with s_k=a. Since B_k<=1,
L_k<=1-a<1-m, while the other three L_i<=2. Apply (H):

    m/(1-m)+3m/2 < 1.                                 (19)

Multiplying by 2(1-m)>0 gives (3m-1)(m-2)>0. Since m<1, this yields m<1/3.
If eta(r)=0 the same upper bound is immediate. Continuity and compactness of
the entire unit reward cube show its attained worst value Omega also satisfies
Omega<1/3.

The proof produces a universal upper bound on infimum exploitability; it does
not assert a terminating profile producer below an arbitrarily chosen
smaller constant, let alone at every positive error.

## 9. Exact regression evidence and noncoverage tests

The companion VERIFY_GENERIC_SCREENED_ROOT_EXCLUSION.py and its recorded
GENERIC_SCREENED_ROOT_CHECKS.json report successful checks of:

- 24 bounded rational nonvanishing witnesses, one for each degree-six factor;
- 144 screened-root full-debt branch comparisons;
- 600 cofactor-nullspace identities;
- 576 invariance checks under arbitrary changes of all four own singletons;
- 18 equal-positive-debt exceptional roots, including three-sure and four-sure
  boundary cases; and
- 32 exact first-order harmonic-ledger coordinate identities, using degree-four
  rational polynomial interpolation.

The exceptional equal-debt fixtures have all own singletons zero, so all Never
is exact Nash. They deliberately have Pi=0 and are NOT positive global minima.
They show why the proof must retain both genericity and global minimality.

The JSON also gives an exact rational table on which all 24 factors are
nonzero. Its smallest absolute factor is 223/4096. This is a nonvanishing
fixture, not a claimed counterexample.

A second nonvanishing fixture lies within 3/4000 of one quarter of the raw
sure-anchor table in ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO. Its parent is
in the supplied explicitly solvable neighborhood, but its screened-root
minimum is strictly above 1/20. Here is a proof of that latter diagnostic,
so its scope does not rely on numerical minimization.

At the unscaled anchor table and at any screened root,

    d_0=max(1,2q_2)-[q_0+2(1-q_0)q_2],
    d_1=max(2q_0-1,0)-q_1(2q_0-1),
    d_2=max(2q_1-1,0)-q_2(2q_1-1),
    d_3=1-q_3.

Setting q_3=1 cannot increase any debt. Some active q_i must then equal one.
In each of the three cases, a bound E<=e<1/2 forces

    e >= (1-e)(1-2e)/2.

For example, q_0=1 gives q_1>=1-e and q_2<=(1+e)/2; then
 d_2=(1-q_2)(2q_1-1)>=(1-e)(1-2e)/2.
The other two cases follow by cyclically following these three displayed
gap equations: q_1=1 gives q_2>=1-e, q_0>=(1-e)/2; q_2=1 gives
q_0<=e, q_1>=(1-e)/2. Equalities are attainable. Therefore the exact
screened minimum is

    e_*=(5-sqrt(17))/4.

Scaling the rewards by 1/4 scales this minimum by 1/4. Since sqrt(17)<33/8,
e_*/4>7/128. Reward perturbation by at most 3/4000 changes every screened
regret by at most 3/2000. The second fixture therefore has

    theta(b)>7/128-3/2000>1/20.

Its one-sure parent equilibrium is supplied by the anchor packet's neighborhood
construction; its distance after rescaling back is at most 3/1000<1/8.
The example explicitly prevents interpreting theta>0 or Pi!=0 as an
all-behavior exploitability gap. The theorem only proves the additional strict
comparison theta>Omega_b when that fiber has Omega_b>0.

## 10. Source correspondence and formalization boundary

Repository reads used the exact main head
5aac30ad2553dadd5895dc79fbc4f1f5680d7570, retrieved during this response.
AGENTS.md was read first. The following exact source declarations were
inspected; this records source reads, not a fresh Lean build or axiom audit.

- minimumTerminalSemantic_maximumDebt_allPlayersTie and
  quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum,
  UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean.
  The file also contains the existing strict-half bound and the all-Never
  nonattainment lemma. The all-player ties are dependencies, not new here.
- minimumTerminalSemantic_exploitabilitySingletonMargin,
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean,
  used by the inspected all-player-tie proof. Its elementary argument is
  reproduced in Section 2.1.
- exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin,
  UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean.
  This is the exact same-pair/same-law unpadded realization used in Section 6.
  Its additional stationary-repetition conclusion is not needed.
- quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential,
  UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean,
  was inspected while considering the alternative polynomial-potential route.
  It is not a premise of the present reduction. Pi is a reward-table
  discriminant, NOT a potential certificate on payoff annotations.

The attached MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION supplies
the common-calendar source construction; its Sections 4-6 are the part reused
in Section 7.2. The new reduction strictly strengthens its pure sure-coalition
floor to ALL screened mixed roots. It does not preserve its exact original
stretch ancestry. The attached THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS
retains an opposed-reversal residual; the generic fiber reduction eliminates
that source case and the two-sure case together, without solving the old
one-variable comparison on an arbitrary incoming table.

The raw table and solvable-neighborhood comparison in Section 9 are from the
attached ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO; only the screened-root
minimum e_* and its use as a noncoverage diagnostic are calculated here.

A bounded repository search for the cofactor/resultant screened-root argument
did not locate a corresponding declaration. No worldwide priority claim is
made. No external original-paper theorem is used beyond standard finite-game
Nash existence and elementary compactness, linear algebra, and polynomial
facts.

A narrow formalization can be organized as follows:

1. The exact screened-root debt formulas, including both optional best-action
   labels and every late finite response and Never.
2. The 3-by-4 cofactor nullspace identity and its quadratic-kernel exclusion.
3. The 24 coefficient constructions, own-singleton invariance, nonvanishing
   witnesses, and density of rational nonvanishing b.
4. Strict screened-root separation at a positive fiber maximum, consuming the
   existing all-player-tie declaration.
5. The independent-law Never implication (15), exact product-base consumer,
   and joint-carrier compact singleton collar, including its varying-table
   graph closure if the fiber-uniform form is desired.
6. Separately, the actual product-prefix first derivative and harmonic bound.

The existence of a good perturbation, a strict screened gap, and a singleton
collar belong in the proved outputs, not assumed certificate fields. No Lean
compiler was found in the local runtime. No Lean file was created or checked,
and no source was published.

## 11. Exact remaining gap

This is not a proof of four-player uniform equilibrium. A hypothetical
counterexample may still have positive singleton mass at all its minimum
laws; that is now the source one may assume. A paid response can still move
caps, create debt in other coordinates, or alter the terminal law, and no
same-source renewable descent is supplied by (16).

It is also not a theorem that generic games have zero exploitability. Pi
excludes a very specific fully tied screened-root configuration. Generic
counterexamples, if they exist, must instead live in the singleton-bearing
minimum branch. The strict one-third bound leaves a nonempty numerical range
for a possible positive gap.

The completed change is therefore: a rational generic singleton-fiber source
with a uniform strict gap for ALL screened roots, and a positive prescribed
singleton-mass collar for every sufficiently accurate actual source in its
positive-gap region. The all-zero-singleton branch no longer needs to be
consumed to decide counterexample existence.
