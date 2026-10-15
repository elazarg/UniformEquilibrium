# Maximum-debt minima: equalization, harmonic obstruction and whole-prefix escape

Status: ordinary UNREVIEWED supporting mathematics, not a new UE reward
class, a counterexample, or an export candidate. This continues the
unrestricted whole-calendar investigation while its earlier notebook and
the graph-free packet remain frozen for independent checks. The objective
here is the GLOBAL maximum debt, not the global total debt and not a
constrained H/J chamber minimum. No minimum-specific result is transferred
between those three objectives.

The exact question is whether a positive minimum of the controller--tester
value has usable geometry beyond the existing total-debt singleton margin.
The theorem below puts EVERY coordinate on the maximum-debt face and gives
a sharp first-order harmonic obstruction. A literal actual calibration
then shows that the obstruction can hold strictly at an unsolved-by-small-
prefix state of a solved table; a distant non-Nash prefix escapes it. Thus
this is a reduction of the minimum geometry, not a completed mechanism.

## 1. Data, agency and checked overlap

Let I be a finite nonempty player set and r_i(S) arbitrary finite real
rewards on nonempty coalitions. Live and Never pay0. Prescribed clocks
are independent private laws on natural dates plus Never. A replacement
is an ENTIRE one-player law, not a finite menu or restricted controller.
Put s_i=r_i({i}); no sign restriction is imposed here.

For an actual profile let U_i be its terminal payoff and B_i the supremum
of all complete unilateral replacements. Its value is equivalently the
supremum of ALL pure finite deadlines and Never. Let K be the closure of
ALL actual pairs(U,B), and write d_i=B_i-U_i>=0 and E=max_i d_i.
K is compact and preserved by every fixed independent product prefix.
Its attained minimum eta is the literal controller--tester value; eta=0
is equivalent to fixed-target uniform-equilibrium existence against all
unrestricted behavioral deviations.

Bounded source inspection:

- `quittingControllerTester_reachableClosure_eq_carrier`,
  `quittingControllerTesterValue_eq_minimum_rawMaximumDebt` and
  `quittingControllerTesterValue_eq_zero_iff_exists_uniformEquilibriumPayoff`
  in `UniformEquilibrium/Quitting/ControllerTester/ControllerValue.lean`.
- The carrier and prefix definitions in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`, and the arbitrary-root
  debt identity in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.
- `quittingTerminalSemantic_minimum_positiveDebt_singleton_le` and the
  exact-root equality face in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`.
  Those minimize TOTAL debt, not E. The stronger total-debt margin is
  used by `minimumTerminalSemantic_nonnegativeWeight_lowerBound` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`.
- The cone alternative in
  `MathUE/LinearAlgebra/FiniteConePositiveAlternative.lean` has different
  strictness conventions. The elementary finite separating argument
  needed below is proved explicitly rather than asserted to be that
  exact declaration.

A narrow phrase/symbol search in these chosen controller/semantic-root
files found no packaged all-equal-debt or harmonic statement for an E
minimum. This is not a claim of a global repository novelty audit.

## 2. Exact prefix account

For a product root q, let c=product_j(1-q_j) and
alpha_i=product_(j!=i)(1-q_j). Against its opponent root let Q_i be the
forced-Quit expectation, b_i the payoff contribution from nonempty
opponent absorption, C_i=b_i+alpha_i B_i, and g_i=Q_i-C_i. Then

    B_i'=max(Q_i,C_i),
    d_i'=c d_i+Delta_i,
    Delta_i=q_i(-g_i)_+ +(1-q_i)(g_i)_+ .                 (M1)

This retains every early, simultaneous, late and Never response. For
fixed q it is continuous and preserves K, including at nonactual closure
points. A full finite cap-Nash root has Delta_i=0 for EVERY player,
including inactive ones, and therefore E'=cE. If q is nonzero then c<1.

## 3. A zero-diagonal finite alternative

For any nonempty finite index set T and real matrix h on T, exactly
one of the following can occur:

    (a) z>=0, sum_i z_i=1, hz<=0;
    (b) w>=0, sum_i w_i=1, w-transpose*h>0 in every column.

If the compact convex image {hz:z in the simplex} meets the nonpositive
orthant, choose the meeting point and obtain(a). Otherwise the image
and that closed orthant are strictly separable: their distance is
positive because the image is compact. A separating functional is
nonnegative, since the orthant is unbounded in every negative coordinate.
Its supremum over the orthant is0. Normalize the nonzero functional to
sum w=1. Strict positivity on the entire image gives(b), including at
each image vertex. Conversely w-transpose*hz cannot be both nonpositive
by(a) and strictly positive by(b). This proves the exact alternative.

## 4. Geometry of EVERY positive global E minimum

THEOREM. Suppose (U,B) in K minimizes E globally and eta=E(U,B)>0.
Then, writing beta_i=B_i-s_i,

    B_i>s_i for EVERY i,
    B_i-U_i=eta for EVERY i,
    eta sum_i(1/beta_i)<=1.                              (M2)

For at least two players, U_i>s_i for EVERY i follows as well. The
statement does not assert total-debt minimality or actual attainment of
the displayed profile.

Proof of the strict cap margins. A nonzero full cap-Nash root would
give E'=c eta<eta by(M1), contradicting global minimality. Therefore
all Continue is the ONLY full cap-Nash root. In particular B>=s.
Suppose its tied set T={i:B_i=s_i} is nonempty. Put

    h_ij=r_i({i,j})-r_i({j}) for distinct i,j in T,
    h_ii=0.

Apply Section3. In case(a), prefix q_i=tau z_i for i in T and0 outside.
At tied coordinates finite polynomial expansion gives
g_i=tau(hz)_i+O(tau^2). Thus (g_i)_+=O(tau^2),
(-g_i)_+=O(tau), and Delta_i=O(tau^2), even if z_i=0.
Outside T, g_i(0)=s_i-B_i<0 and q_i=0, hence Delta_i=0 EXACTLY for
all sufficiently small tau. Also c=1-tau+O(tau^2). Consequently
E'<=eta-eta*tau+O(tau^2)<eta, contradiction.

In case(b), add epsilon>0 to the Quit payoff of EVERY tied player in
the finite Boolean game with continuation B. Choose any finite Nash
root q^epsilon. Compactness and closed Nash inequalities imply
q^epsilon->0: every subsequential limit is original Nash, hence0.
For small epsilon all outsiders remain pure Continue by their strict
negative gap at0. With t=sum_(i in T)q_i, finite expansion and(b) give

    sum_i w_i g_i(q)>=mu*t-C*t^2>=0

near0, for some mu>0 and finite C. Perturbation adds epsilon sum w_i
=epsilon, making the weighted gap positive. Some tied player therefore
strictly prefers Quit and has rate1, contradicting q^epsilon->0.
Both alternatives fail, so T was empty. No H/J, participant-flatness,
inverse sign or supplied root selector was used.

Proof of equal debts. Suppose d_j<eta. Prefix only player j with a
small positive rate tau. All caps have strict singleton margin, so for
small tau every g_i remains negative. For i!=j, Delta_i=0 and
d_i'=(1-tau)d_i. For j, its opponent root is identically Continue,
g_j=s_j-B_j=-beta_j, so

    d_j'=(1-tau)d_j+tau beta_j.

The strict old slack eta-d_j keeps this below(1-tau)eta for sufficiently
small tau. Every other coordinate is at most(1-tau)eta. This again
contradicts global minimality. Hence d_i=eta for every i.

Proof of the harmonic inequality. Put H_*=sum_i(1/beta_i)>0 and choose
z_i=(1/beta_i)/H_*. Prefix q_i=tau z_i. All gaps remain strictly
negative for small tau. The finite expansions in(M1) give

    c=1-tau+O(tau^2),
    Delta_i=tau z_i beta_i+O(tau^2),
    d_i'=eta+tau[1/H_*-eta]+O(tau^2).

If eta H_*>1, the common linear coefficient is strictly negative and
ALL debts decrease, contradiction. Thus eta H_*<=1. For n>=2, every
positive summand eta/beta_i is strictly below1, so beta_i>eta and
U_i=s_i+beta_i-eta>s_i. This completes the proof.

This is a MAXIMUM-debt result. The total-debt objective at this point
equals n eta, but it has NOT been shown to minimize total debt. The
checked total-minimum inert-update and source-renewal conclusions may
not be attached to this point without a separate argument.

## 5. Exact actual calibration: first-order stability is feasible

Here is a complete four-player original table, with unit own singletons
and live/Never0:

    0:(1,0,4,0)          1:(0,1,0,4)
    2:(4,0,1,0)          3:(0,4,0,1)
    01:(-1,2,3/2,3/2)    02:(0,2,0,2)
    03:(2,3/2,3/2,-1)    12:(3/2,-1,2,3/2)
    13:(2,0,2,0)         23:(3/2,3/2,-1,2)
    012:(-1,-1,-1,10)    013:(-1,-1,10,-1)
    023:(-1,10,-1,-1)    123:(10,-1,-1,-1)
    0123:(9,9,9,9).

All four players Quit0 surely. Its ACTUAL pair is U_i=9,B_i=10 for
every i: Continue/Never against the three opponents' sure quits earns10,
while Quit earns9. Thus every debt is1, beta_i=9 and
eta sum_i1/beta_i=4/9<1 when the displayed debt1 is inserted in the
harmonic test. This does NOT make the point a global minimum.

In fact it is a strict local minimum of E under nonzero small product
prefixes. Let t=sum_i q_i. Near0 all g_i stay negative, and(M1) gives

    d_i'=1-t+9q_i+O(t^2).

Choose an index with q_i>=t/4. Then E'>=1+(5/4)t-Ct^2>1 for all
sufficiently small t>0. The remainder is uniform over the finite unit
simplex. Hence NO infinitesimal independent prefix improves this actual
state, despite its strict positive debt and completely legal agency.

A distant NON-Nash prefix does improve it. Take

    q=(1,0,0,3/4).

Direct full-response calculation gives

    U'=(7/4,9/8,17/8,-3/4),
    B'=(5/2,9/8,17/8,0),
    d'=(3/4,0,0,3/4).

For player0, Quit now gives7/4; Continue gives(1/4)*10+(3/4)*0=5/2.
Players1,2 get their prescribed passive expectations by Continue, while
their immediate joining endpoints are-1/4 and-3/4. Player3 chooses
Continue0 over Quit-1. These are the ENTIRE full caps after the prefix,
including the retained old tail. Thus E'=3/4<1 exactly. The root is
not Nash: player0 is surely choosing its worse root endpoint. This is
funded full-cap accounting, not a late-only estimate.

The minimum geometry therefore rules out tied caps and unequal debts at
a true positive E minimum, but a strictly feasible harmonic obstruction
already occurs at a literal actual state. A universal infinitesimal-
prefix proof is false; the missing global step must use distant prefixes,
old-law changes, or another operation with complete response accounting.

## 6. Concrete next question and nonclaims

Can the equal-debt positive E-minimum face be shown to admit one distant
finite product-prefix WORD with smaller maximum debt, using only actual
carrier semantics and the hard Fin4 singleton matrix? The calibration
shows why neither a tied-cap dispatch nor an infinitesimal vector field
is an exhaustive answer. It does not support a guess that every
nonminimum local stall has a one-root escape, or that the displayed
two-player-support root works for arbitrary collision rewards.

The theorem above supplies neither that word nor a new raw UE class.
It has not been independently reviewed or checked in Lean. The finite
grid used to discover the calibration root was only a search device;
the literal root and ALL response endpoints above are exact, and no
claim about the grid's global optimum is used.
