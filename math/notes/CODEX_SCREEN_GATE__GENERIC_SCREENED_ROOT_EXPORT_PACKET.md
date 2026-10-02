# Generic screened-root exclusion and a singleton-mass collar

Authors: the author of the user-supplied
[GENERIC_SCREEN](../gpt/GENERIC_SCREEN.md) and its
[full proof](../gpt/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md);
the source does not identify a separate author name. Export assembly:
CODEX_SCREEN_GATE. The common-calendar source construction is due to
CODEX_NOETHER_SUPPORT and the contributors credited in its dependency below.

Independent reviews:
[CODEX_CAYLEY_SCREEN](../feedback/GENERIC_SCREEN_EXPORT__BY_CODEX_CAYLEY_SCREEN.md),
[CODEX_PORTMANTEAU_SCREEN](../feedback/GENERIC_SCREEN_EXPORT__BY_CODEX_PORTMANTEAU_SCREEN.md).

The new results below are ordinary mathematics, not new Lean-checked
declarations. The prior complementary reviews of the supplied proofs are
[algebra and fiber selection](../feedback/GENERIC_SCREEN__BY_CODEX_CAYLEY_SCREEN.md)
and [semantics, compactness, and source attachment](../feedback/GENERIC_SCREEN__BY_CODEX_PORTMANTEAU_SCREEN.md);
their [combined review](../feedback/GENERIC_SCREEN__BY_CODEX_COORDINATOR.md)
records no unresolved objection within those prior scopes.

## Conjecture-facing change and exact admission

This packet is a counterexample-preserving reduction for four players.
Existence of any real reward table without a uniform-equilibrium payoff is
equivalent to existence of a rational interior 56-coordinate fiber satisfying
Theorems A–C below, with a positive maximizing table and the actual
common-calendar source specified in Section 7.2. The reverse implication uses
that table's positive infimum of maximum unrestricted terminal regret.
The forward implication produces the generic fiber, its strict screened-root
gap, and its singleton collar; none is assumed of the incoming table.

The named prior obligation is the strict-gap singleton-pressure source of
Sections 4–7 of
[MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md).
Its eleven pure nonsingleton sure-coalition exclusions are strengthened to
every product root having at least two sure quitters, including mixed roots.
The zero-singleton minimum-law branch, and hence the opposed three-sure
residual of
[THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS](../exports/THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md)
and the two-sure case, can be omitted after this source selection. The old
incoming-table comparison is not proved for arbitrary tables by this result.

The remaining obligation is to improve the full maximum regret of the
singleton-bearing source, controlling all players' changed response caps.
This packet does not solve that obligation or the finite-quitting conjecture.

### Strategic inputs and their producers

The only conjecture-side premise of the forward reduction is a hypothetical
four-player counterexample, equivalently a real table with eta>0. All further
inputs are produced as follows.

- A common positive scale puts its rewards strictly inside the unit cube.
  Reward robustness, polynomial nonvanishing, and rational density then
  select b; compact singleton maximization selects s_* and Omega_b>0.
  Section 5 produces the rational strict gap gamma.
- Compact closures of actual semantic pairs and joint outcome laws produce
  minimizing points and simultaneous approximating sequences (Sections 2,
  6, and 7). No actual attainment of the global infimum or of a response cap
  is required.
- Finite normal-form Nash existence produces the auxiliary product root in
  Section 2.1. Its continuation annotation is explicitly supplied from the
  chosen carrier pair; it is not assumed to be a behavioral payoff.
- If a minimizing law had no singletons, Section 6 first proves zero Never
  and strict singleton margins. The named exact product-base realization
  theorem then produces the screened root with the same complete pair and
  law, yielding the contradiction. That theorem needs no ancestry or
  externally supplied clock.
- Compactness produces kappa and epsilon_0, uniformly on every fixed
  positive-gap portion of the selected fiber (Section 7).
- Reward-uniform finite-clock approximation, compact finite optimization,
  projected gradient separation, and the common-calendar selection in
  Sections 4–6 of the membership-fiber dependency produce all actual finite
  profiles and their tester weights. Section 7.2 states the retained
  conclusion exactly and proves the added collar on those same profiles.

There are no unproduced strategic witnesses required by these conclusions,
and no conditional-result exception is requested. The construction is
existential; it is not an algorithm for deciding whether eta>0 or for
computing an accuracy-independent positive gap. No recursive source
regeneration is claimed or used.

## 1. The result

The player set is I={0,1,2,3}. Every nonempty quitting coalition S pays r(S) in R^4;
live play and Never pay zero. Strategies and deviations are unrestricted
behavioral strategies with independent private randomization. Equivalently,
players independently choose clocks in N union {Never}, where N starts at zero.
The first finite clock time absorbs with the entire simultaneous quitting
coalition. Before absorption the only public history is repeated
all-Continue; independent private hazards along that history define exactly
these independent stopping laws, including their Never atoms. Conversely
each such law has its conditional behavioral hazards. A deviator replaces
one entire law and can use unbounded time and Never, but cannot observe
opponents' private clocks. There is no public correlation device.

All payoffs, debts, and masses below are unconditional expectations from the
live state. No conditional deviation claim is inferred from them. A fixed
pure response means one deterministic finite clock or Never. Averaging over
a deviator's clock shows that the supremum over all its laws equals the
supremum over these pure responses, without an attainment assumption.

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

The first expression does not depend on s. Both extrema are attained, as
proved in Section 5. The infimum eta need not be attained by an actual
profile; its carrier minimum is attained.

Here eta(r)>0 is equivalent to absence of a uniform-equilibrium payoff.
For eta>0 and any actual profile, some player's cap gain is at least eta,
so a complete response gains more than eta/2 by the definition of supremum.
Conversely a fixed positive gain against every profile lower-bounds eta.
The existing terminal-gap equivalence in Section 10 gives the stated
semantic equivalence. Its positive endpoint chooses one fixed payoff
target before the requested accuracy; for each accuracy one behavioral
profile must control every sufficiently long finite horizon. No discounted
or finite-horizon claim is silently substituted for the terminal statement.

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
approximant. The common-calendar source in the membership-fiber dependency can be selected
with this additional field, without changing its profiles, labels, or
weights; Section 7.2 gives its exact quantifiers.

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

and write w_i(S)=prod_(j in S)q_j prod_(j not in S, j!=i)(1-q_j)
for S contained in I without i. Precisely,

    Q_i=sum_(S subset I\\{i}) w_i(S) r_i(S union {i}),
    H_i=sum_(nonempty S subset I\\{i}) w_i(S) r_i(S).

Thus Q_i is player i's Quit-now reward and H_i is its absorbing contribution
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

Fix a sure pair K={a,b}, with a<b in the order 0<1<2<3; order
the other players c<d. These fixed orders define every polynomial factor. Their independent
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

### 7.2 The same actual common-calendar source with the collar

Here is the precise retained conclusion of the
[membership-fiber source](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md),
Sections 4–6, together with the new field. This is a use of that proved
construction after the new initial fiber selection.

For each N let X_N be the product, over the four players, of probability
simplices on {0,...,N-1,Never}. For an actual p, a pure response label (i,t)
has gain

    g_(i,t)(r,p)=U_i^r(p[i<-t])-U_i^r(p).

There is also a separate zero tester with gain zero. Its reward-coefficient
vector is zero; that of (i,t) is zero for recipients other than i, and its
(i,S) coordinate is the response outcome mass at S minus the prescribed
outcome mass at S. Let D_p g_a(r,p)[nu-p] denote the derivative at beta=0
along the independent marginal chord p_j(beta)=(1-beta)p_j+beta nu_j for
every player j. This is a product of mixed marginals, not a correlated
mixture of the two joint profiles.

There are fixed b, gamma, Omega_b, r_infty=r_b(s_infty), and kappa>0 with
eta(r_infty)=Omega_b>0, followed by actual finite independent profiles p_m
and weights lambda_m, such that N_m tends to infinity and:

1. p_m has finite dates among 1,...,N_m and Never, so it is silent at zero.
   Its full exploitability at r_infty tends to Omega_b. Every screened root
   q satisfies E_(r_b(s))(q)>=Omega_b+gamma for every s.
2. lambda_m is a probability vector on the complete finite response pool
   through N_m+3, the distinct Never response for each owner, and zero.
   Uniformly for every simultaneous independent competitor
   nu in X_(N_m+3),

       sum_a lambda_(m,a) D_p g_a(r_infty,p_m)[nu-p_m] >= -o(1).

3. The same weights satisfy

       sum_a lambda_(m,a)[E_(r_infty)(p_m)-g_a(r_infty,p_m)] -> 0.

4. Each owner weight theta_(m,i)=sum_t lambda_(m,i,t) is eventually at least
   Omega_b/4.
5. The same profile and weights satisfy the total pressure inequality

       limsup_m sum_(i,t) lambda_(m,i,t)
          [mu_(p_m[i<-t])({i})-mu_(p_m)({i})] <= 0.

6. Every selected source has

       sum_i mu_(p_m)({i}) >= kappa.                      (16)

In particular, the fixed data precede every accuracy epsilon>0 and requested
calendar depth d: one can choose N>=d and one such actual profile and weights
with exploitability error, directional error, inactivity, and the upper pressure
bound at most epsilon, all four owner weights at least Omega_b/4, and (16).
A subsequence has one fixed owner with total singleton mass at least kappa/4.
The scalar pressure statement is not four coordinatewise inequalities.

To verify the attachment, the predecessor's Sections 4–6 require only a fixed
fiber, its positive maximizing value, a strict nonsingleton pure-root floor,
reward-uniform complete finite approximation, and the MAX singleton moat.
They do not use its earlier common stretch or original-table comparison.
Theorem B supplies those premises, with a stronger screened-root floor.

For clarity, the finite approximation is uniform over this whole fiber:
for every N>=m it gives

    eta(r)<=min_(p in X_N) E_r(p)<=eta(r)+rho_m,  rho_m -> 0.

The source proof takes tau=m^(-1/2), L=2m+1, and the common labelled pool
J={zero} union (I times {0,...,L,Never}). It minimizes
F=tau log sum_(a in J) exp(g_a/tau) over each X_N, m<=N<=2m, and maximizes
the average of these minimum values over s in the compact singleton cube.
Since E<=F<=E+tau log|J| on X_L, its selected tables r_m satisfy
eta(r_m)->Omega_b; every inner minimizer in every calendar of the window
has E-eta(r_m)->0 uniformly. Compactness selects r_m->r_infty with
eta(r_infty)=Omega_b.

The cited construction then uses projected four-coordinate gradient
separation, its common-table calendar telescope, a silent shift, and
same-weight selection to prove fields 1–5. It provides these finite
profiles and weights, not an assumed stationarity certificate.

Apply Section 7.1 with a=Omega_b/2. Every sufficiently late actual inner
minimizer has singleton mass at least one common kappa before any tuple or
calendar selection. The silent shift preserves the terminal outcome law.
Discarding calendars, choosing a tuple entry, and retaining or transporting
tester weights preserve this fact. Evaluating the same laws at r_infty also
leaves their law unchanged. Thus fields 1–5 and (16) hold on the same chosen
profiles and weights. Discarding finitely many initial indices gives the
form above. Finiteness of I proves the fixed-owner subsequence assertion.

The weights at r_infty are transported weights computed at the nearby
tables; they are not asserted to be fresh softmax weights there. Tuple
mixtures used in the optimization are not played as a game strategy.
No individual source has an asserted reward normal, and no normality in
the 56 frozen coordinates or full sixty-coordinate norm identity survives
as a claimed field.

The owner bound is on TOTAL prescribed first-coalition singleton probability.
It gives no fixed date, response-law singleton bound, cap-attaining response,
actual minimizing-profile realization, or post-response cap control.

## 8. An additional harmonic constraint and the strict one-third bound

This calculation is independent of genericity. It applies to every positive
maximum-debt minimum of every unit-bounded finite-player game. Continue to
write d_i=m and L_i=B_i-s_i>=m.

For positive rates lambda_i and a small t>0, prefix ONE independent product
root with q_i=t lambda_i. Because B_i>s_i at t=0, all complete-cap branches
remain Continue for sufficiently small t, by continuity of the finitely many
endpoint gaps. Equation (1) then has the first-order expansion

    d'_i=beta_i d_i+q_i(H_i+beta_i U_i-Q_i)
         =m+t[lambda_i(U_i-s_i)-m sum_{j!=i}lambda_j]+O(t^2)
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
These are MAXIMUM-debt minimum statements. No minimum of TOTAL debt is used.

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

The archived companion VERIFY_GENERIC_SCREENED_ROOT_EXCLUSION.py and recorded
GENERIC_SCREENED_ROOT_CHECKS.json report the following checks, reproduced by
the prior algebra reviewer with the file-writing main block disabled:

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
sure-anchor table in
[ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO](../exports/ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md).
That complete raw table is

    r*_0(S)=1 if 0 in S, and 2*1_(2 in S) otherwise,
    r*_1(S)=(2*1_(0 in S)-1)*1_(1 in S),
    r*_2(S)=(2*1_(1 in S)-1)*1_(2 in S),
    r*_3(S)=1_(3 in S),

for every nonempty S. Its exact one-sure equilibrium is
q=(1/2,1/2,1/2,1), with U=B=(1,0,0,1). The first three players' Quit0
and Continue payoffs tie, and player 3 attains its global reward upper bound.
The perturbed fixture lies in the scaled explicitly solvable neighborhood,
and its screened-root minimum is strictly above 1/20.
Here is a proof of that latter diagnostic,
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
q_0<=e, q_1>=(1-e)/2. Equality is attained at
q=(1,1-e_*,(1+e_*)/2,1). Therefore the exact
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

The neighborhood countertest does not depend on trusting a sampled
nonvanishing fixture: rational points with Pi!=0 are dense by Section 4.1,
so there are such points within the displayed rational neighborhood of
r*/4. The cited anchor construction gives an exact one-sure equilibrium at
each table there, and the calculation above gives theta>1/20 throughout
that neighborhood. Thus genericity and positive screened regret coexist
with eta=0.

As an elementary degenerate test, the all-zero table has Pi=0, eta=0, and
an all-Never zero-singleton minimizer. The strict positive-gap hypothesis
of the singleton collar cannot be discarded.

### 9.1 Archive integrity and reproducibility

The original [short manuscript](../gpt/GENERIC_SCREEN.md), its stable
[sibling full proof](../gpt/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md),
and the [three-member archive](../gpt/GENERIC_SCREENED_ROOT_REDUCTION.zip)
are retained unchanged. The archive contains the full proof, the exact
Python checker, and its JSON results under the filenames just stated.
The archived proof is byte-identical to the sibling full proof. Their
SHA-256 identities are:

- Short manuscript:
  `55403cec9d8481cc161c835c5588196b8fedf898ecc74c1745b2c9cfbc948a6e`.
- Full proof:
  `07df0dcef1bb37d9c1721a1147981fcbe2069719eff263f608a7534f907752cc`.
- Archive:
  `d0091a1bf36d27324e451e7c8651b83cbd2e125984cdd83d510ca3763880a56c`.

With Python and SymPy available, run the following from math/ after
inspecting the archived script. It extracts nothing and avoids its
file-writing main block:

```sh
python - <<'PY'
import json
import zipfile
with zipfile.ZipFile("gpt/GENERIC_SCREENED_ROOT_REDUCTION.zip") as archive:
    name = "VERIFY_GENERIC_SCREENED_ROOT_EXCLUSION.py"
    source = archive.read(name).decode("utf-8")
    expected = json.loads(archive.read("GENERIC_SCREENED_ROOT_CHECKS.json"))
namespace = {"__name__": "screen_regression_review"}
exec(compile(source, name, "exec"), namespace)
actual = namespace["run_checks"]()
assert json.loads(json.dumps(actual)) == expected
print(json.dumps(actual["counts"], indent=2))
PY
```

These finite checks are regression evidence. They do not prove genericity,
positive gap existence, compactness, or any unrestricted universal claim;
the mathematical proofs in this packet and its named theorem dependencies
supply those arguments.

## 10. Source correspondence and implementation boundary

The following declarations and their relevant imports were inspected during
assembly, following the boundary-analysis and zero-singleton product-base
entries of docs/TOOLKIT.md. This is a static source audit, not a fresh Lean
build or axiom audit. The source correspondence uses declaration names and
files, without line-pinned citations.

- `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean` is the finite-quitting
  target proposition, not a proved general existence result.
- `quittingContinuationBestResponseValue` in
  `UniformEquilibrium/Quitting/Root/FirstBranch.lean` is explicitly the
  supremum over every unilateral `BehaviorStrategy`.
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
  identifies it with the supremum over finite pure dates and Never.
  This is the full response scope in Sections 1–3 and 7.2.
- `minimumTerminalSemantic_maximumDebt_allPlayersTie`,
  `terminalSemantic_minimum_of_actualMinimum`, and
  `quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum`
  in `UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`
  supply the carrier tie and actual-minimum bridge. The unit reward bound
  is present. Their elementary tie proof is reproduced in Section 2.2.
  The same file's `minimumTerminalSemantic_maximumDebt_lt_half` is the
  existing strict-half bound improved here by Section 8.
- `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`
  gives the MAX singleton moat; Section 2.1 reproduces its finite-Nash
  argument. Its objective is the same maximum debt used throughout.
- `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
  in `UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`
  consumes joint-carrier membership, zero Never, zero singleton masses,
  at least two players, and s_i<B_i for every i. It produces an UNPADDED
  root-then-Never realization of the full pair and law, with two distinct
  sure quitters. Its extra stationary-repetition conclusion is unused.
  This is an existing theorem dependency of Section 6, not a deferred
  new lemma or a strategic witness hypothesized in the final result.
- `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` and
  `quittingTerminalExploitabilityInf_scaleQuittingReward` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
  give the exact 2-Lipschitz and scaling facts reproduced in Section 5.
  This is the current source path; the older membership-fiber packet's
  Research path for these declarations is not used here.
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket`,
  `quantileClockSupport_fin4`, and
  `exists_finiteClockSemanticPair_exploitability_eq_upper` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` provide
  actual finite-clock approximation with support 8k+1 and objective error
  at most 24/k. The normalized bracket supplies the compression argument
  via `hasEscapeAwareQuantileClockCompression_of_normalized`; no open
  compression assumption is added. These are Research dependencies,
  without a new production-integration or axiom-audit claim.
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  are the negative and positive semantic endpoints. The former makes this
  an exact counterexample-existence reduction; the latter remains a
  possible downstream consumer if arbitrarily low-regret profiles are
  eventually produced. This packet does not supply them.

The [membership-fiber source dependency](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md)
provides the complete ordinary-mathematical common-calendar construction.
Only Sections 4–6 after its initial fiber choice are reused. The
[opposed-reversal dependency](../exports/THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md)
identifies a prior residual removed from the newly selectable source; its
old-table stretch relation is not a premise retained here. The
[anchor dependency](../exports/ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md)
supplies the exact solved neighborhood for the noncoverage test.

A bounded search in the quitting diagnostics for screened-root generic
polynomials, cofactor exclusion, and a singleton-mass collar found no
equivalent implementation of the new result. The literature lane's scope
instructions were read, and a narrow corresponding phrase search found no
paper transcription supplying it. No publication-priority claim is made.
The proof uses no external specialized paper theorem; finite normal-form
Nash existence, elementary finite-dimensional compactness, polynomial
facts, and linear algebra are standard dependencies.

The new content consists of the explicit degree-144 reward polynomial,
the strict screened-root fiber separation and rational selection, the
zero-Never argument at a zero-singleton MAX minimum, the prescribed-mass
collar including its fiber-uniform form, the attachment of that collar to
the same actual common-calendar source, and the independent harmonic
and strict one-third bound. The all-player ties, full-cap product-base
realization, and common-calendar producer are credited dependencies.

## 11. Lean handoff

Keep the new claims separate from already available theorem dependencies.

1. Define the four-player 56-coordinate projection and singleton fiber,
   screened product roots, the ordered branch matrix, its signed maximal
   minors, and Pi. Derive the exact full-debt formulas and own-singleton
   independence, including every probability boundary.
2. Prove the finite 3-by-4 cofactor identity and quadratic-kernel exclusion,
   then the recipient-disjoint bounded witnesses for all 24 factors and
   density of rational nonvanishing b.
3. Combine compact screened-root and fiber extrema with the existing
   all-player tie declaration to obtain strict separation. Use robustness
   and common positive scaling to produce b and gamma from any eta>0
   table; do not assume these outputs as certificate fields.
4. Use the existing joint carrier and product-base theorem after proving
   inequality (15) and the zero-Never conclusion. Prove compact positivity
   of total singleton mass at minima and its actual-profile collar.
   Formalize the varying-reward closed graph for the fiber-uniform form.
5. Reuse the membership-fiber common-calendar construction under its
   actual fixed-fiber premises. Attach the collar before calendar/tuple
   selection, keeping the same profiles, tester pool, weights, and final
   reward transport. The existential b, r_infty, gamma, and kappa must
   precede all accuracy/depth quantifiers.
6. Separately formalize the exact Continue-branch prefix ledger, its
   first derivative, the harmonic inequality, and the strict one-third
   consequence with compact global attainment.

Likely game-semantic objects are the existing semantic pair, joint carrier,
one-date product profile, exploitability infimum, and complete response cap.
The elementary polynomial algebra can be isolated from game semantics.
Finite witness checks should use exact rational arithmetic; an algebraic
fixture is not a counterexample table. The narrowest relevant Lean module
checks and the project's required trust checks belong to future
formalization. No Lean file, build, axiom audit, or new L/A/C seal is part
of this packet.

## 12. Scope and remaining question

This is not a proof of four-player uniform equilibrium. A hypothetical
counterexample may still have positive singleton mass at all its minimum
laws; that is now the source one may assume. A paid response can still move
caps, create debt in other coordinates, or alter the terminal law, and no
same-source renewable descent is supplied by (16).

It is not a theorem that generic games have zero exploitability. Pi excludes
fully tied screened roots, not arbitrary strategy laws. It also does not
preserve an arbitrary incoming counterexample table, its membership-stretch
ancestry, a full sixty-coordinate normal, or fixed-calendar intervention
laws. The maximizing own-singleton vector need not be rational.
The collar is uniform for a fixed selected fiber above each positive
threshold a; it is not asserted uniform as a tends to zero.

No fixed stopping date, counterfactual singleton probability, exact
best-response attainment, positive-minimum actual realization, or
post-response cap bound is inferred from prescribed total singleton mass.
The harmonic result is an independent positive-error restriction, not a
vanishing-regret producer or a terminating algorithm.

The concrete remaining question is whether the selected singleton-bearing
source admits a complete-regret improvement with all changed response caps
controlled. Theorem C and Section 7.2 strengthen its inputs but do not
answer that question.
