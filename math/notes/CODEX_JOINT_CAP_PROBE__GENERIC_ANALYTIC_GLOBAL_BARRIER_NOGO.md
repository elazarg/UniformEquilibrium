# Generic reset interiors exclude every analytic global function barrier

Identity: CODEX_JOINT_CAP_PROBE.

Status: complete ordinary-mathematics proof with an exact finite algebraic
control, not independently reviewed or Lean-checked. This excludes an entire
global certificate grammar. It does not prove A_abs=0, produce a positive-gap
game, or solve Fin4. No new local equilibrium fixture is being proposed.

The theorem concerns functions monotone under EVERY product-root prefix on
the FULL payoff/cap box. Generically, every polynomial function with this
property is constant. Even allowing the four original Never probabilities
as extra variables cannot give a positive function certificate bounded above
by debt on the absorbing face. Closed semialgebraic invariant sets, whose
invariance is required only at their own points, remain outside this result.

## 1. Exact semantic setting

There are four players, independent private stopping laws on the natural
dates and Never, zero live/AllNever reward, and arbitrary real rewards
r_i(S) for the sixty recipient/nonempty-coalition coordinates. Fix a reward
bound M and any R>=M with R>0. Write

    K_R=[-R,R]^4 x [-R,R]^4,
    z=(U,B),
    Khat_R=K_R x [0,1]^4,
    zhat=(U,B,N).

Here U is prescribed terminal payoff and B is the FULL unilateral behavioral
cap, including every finite date and literal Never. The independent-coordinate
box also contains nonrealizable annotations; the global function-certificate
contract deliberately quantifies over those points.

For a product root q in [0,1]^4, put alpha=product_i(1-q_i). Let R(q) be
the unconditional absorbing reward contribution, Q_i(q) the immediate-Quit
payoff, A_i(q) the unconditional passive contribution from opponents quitting
while i Continues, and H_i(q)=product_(j!=i)(1-q_j). The exact prefix map is

    T_q(U,B)=(R(q)+alpha U,
                 (max(Q_i(q),A_i(q)+H_i(q)B_i))_i),
    That_q(U,B,N)=(T_q(U,B),((1-q_i)N_i)_i).             (1)

The map preserves the displayed box. For actual stopping laws it is literal
prefixing, with the original Never probabilities retained exactly. No Nash
assumption is imposed on q or on the continuation annotation.

## 2. The generic theorem

There is an explicit nonzero homogeneous polynomial P in the sixty reward
coordinates, of degree 2048, with the following properties. Its restriction
to the native own-singleton-zero subspace is also nonzero.

**Theorem.** Suppose P(r)!=0.

1. The semantic states obtained from a sure grand-coalition reset by just
   TWO earlier product roots contain a nonempty open subset of R^8.
   Every such profile is actual and absorbs by its third occupied date.
2. Every real-analytic h on a connected open neighborhood of K_R satisfying

       h(z)<=h(T_q z)       for every z in K_R and every q

   is constant on K_R. In particular this holds for polynomials of every
   degree, with arbitrary separate payoff/cap coefficients and cross terms.
3. Let h be any function on Khat_R satisfying

       h(zhat)<=h(That_q zhat)       for every zhat and every q.      (2)

   Assume only that (U,B) -> h(U,B,0) is real-analytic on a connected open
   neighborhood of K_R. Then it is constant on the entire N=0 slice, and
   h everywhere is bounded above by that constant. If additionally

       h(0,0,0)<=0,                                     (3)

   then h<=0 throughout Khat_R.

There is no analyticity requirement on the dependence on N in part 3.
Thus polynomial dependence on all twelve state coordinates is covered,
as is arbitrary extra Never dependence when the N=0 slice is analytic.

Condition (3) follows from the usual full-box pointwise minorant obligations:
raw maximum debt, total debt, their nonnegative parts, and

    sum_i theta_i(B_i-U_i)+lambda product_i N_i

all vanish at the diagonal point (0,0,0). It is enough to impose the
minorant on the N=0 slice. Consequently none of these globally monotone
analytic function grammars can certify a strictly positive floor for a
table with P(r)!=0.

The complement of P=0 is open and dense, both in the full reward space and
in the native own-zero subspace. The exact properness control below even
keeps the previously used strict-inverse-column singleton matrix fixed.

## 3. Why the reset kernel must be a maximum plateau

Let I={0,1,2,3}. The root at which every player quits surely sends every
tail annotation to the SAME point

    c_r=(r(I),(max(r_i(I),r_i(I\{i})))_i).              (4)

A unilateral replacement cannot stop the other three sure quitters, so
(4) is the complete cap, not a bounded tester calculation. In the augmented
state, this reset has original N=0 regardless of the incoming N.

If h obeys (2), its reset value C=h(c_r,0) is a global maximum:
h(zhat)<=C for every input. Applying any further finite root word to that
reset can only increase h, and cannot exceed C. Therefore

    h(That_w(c_r,0))=C                 for every finite root word w. (5)

This part uses no regularity, source minimizer, or equilibrium hypothesis.
It is the universal-reset observation already present in
[SPINOZA's reset-kernel note](CODEX_SPINOZA__UNIVERSAL_RESET_KERNEL_AND_POSITIVE_BARRIER_TOPOLOGY_NOGO.md).
The new point is that a generic reset kernel contains an OPEN semantic set,
which forces analytic functions with (5) to be globally flat on that slice.

## 4. A branch-complete finite polynomial map produces the open set

For i=0,1,2,3 let

    p_i(x)=a_i delta_0+b_i delta_1+(1-a_i-b_i)delta_2,
    x=(a0,b0,...,a3,b3),
    Omega={a_i>0,b_i>0,a_i+b_i<1 for every i}.

These are actual independent laws. They equal two product roots with
hazards a_i and b_i/(1-a_i), followed by the sure grand-coalition reset.
Let U_i(x;r) be prescribed payoff. Let V_i^k(x;r) be the pure-response value
for k=0,1,2,3. Label 3 means any finite date after 2 OR literal Never:
the other three players surely quit by 2, so all these responses agree.
There are no other distinct full-response classes. Hence

    B_i(x;r)=max_(k in {0,1,2,3}) V_i^k(x;r).           (6)

Each U_i and V_i^k is a polynomial in x and is linear in r. Complete
behavioral replacements average the pure stopping-date responses, proving
both inequalities in (6).

For each of the 4^4=256 branch labels kappa in {0,1,2,3}^4, define the
polynomial map

    Phi_kappa(x;r)=(U_0,...,U_3,V_0^(kappa_0),...,V_3^(kappa_3)).

Put x*=(1/4,...,1/4) and define the integer-coefficient polynomial matrix

    K_kappa(r)=64 derivative_x Phi_kappa(x*;r),
    Delta_kappa(r)=det K_kappa(r),
    P(r)=product_kappa Delta_kappa(r).                 (7)

The factor 64 clears every denominator: a prescribed derivative averages
over three other draws with probabilities 1/4,1/4,1/2, and a forced-response
derivative averages over two other draws. Each matrix entry is an integer
linear form in the rewards, so every determinant is homogeneous of degree
8 and their product is homogeneous of degree 2048.

Suppose P(r)!=0. All 256 derivatives are nonsingular at x*, so by continuity
there is one open neighborhood W of x*, contained in Omega, on which they
are ALL nonsingular. We must still handle the maximum in (6); simply
choosing a favorable cap branch would not suffice.

Consider the finitely many polynomial differences V_i^k-V_i^l. Discard
those that are identically zero as polynomials in x. Each remaining zero
set has empty interior. Their finite union cannot cover W. Choose x0 in W
outside that union. In a neighborhood W0 of x0 every nonidentical response
comparison has a fixed strict sign, while identical responses remain equal.
Therefore one fixed branch kappa realizes ALL four maxima throughout W0.
On W0 the ACTUAL full semantic map (U,B) is exactly Phi_kappa.

Its derivative at x0 is nonsingular. The inverse-function theorem gives a
neighborhood whose actual semantic image contains a nonempty open set in
R^8. This image belongs to the reset kernel and lies in K_R. This proves
part 1, without a tie-genericity assumption or an unpriced cap branch.

Equation (5) now makes h(.,.,0) constant on a nonempty open set. The real-
analytic identity theorem makes it constant on the connected neighborhood
of K_R. Its value is C. The reset inequality gives h<=C everywhere,
and (3) gives C<=0. This proves parts 2 and 3.

## 5. Exact properness certificate, with native own singletons zero

Use the singleton matrix

    Gamma = [ 0 -9 -6  7 ]
            [-6  0  4  7 ]
            [ 7  8  0 -1 ]
            [-1 -3  9  0 ].

For the eleven nonsingleton coalitions in this EXACT order,

    01,02,12,012,03,13,013,23,023,123,0123,

use these four recipient rows:

    row 0: [ 5, 6,-3,-1, 6,-7,-6, 3,-9, 3, 7]
    row 1: [-6, 5,-8, 9,-7,-8, 2,-9,-2, 6,-8]
    row 2: [ 3,-1, 1, 9,-5, 9, 0, 3, 9, 5, 8]
    row 3: [ 8, 4, 5, 4,-5,-3,-6,-9, 7,-7, 3].

This specifies all sixty integer entries. The accompanying checker forms
every derivative matrix by exact first-coalition enumeration, evaluates all
256 integer determinants using fraction-free elimination, and obtains

    product_kappa Delta_kappa(r) = 989105  (mod 1000003).             (8)

The nonzero residue proves P(r)!=0 over the integers. It proves properness
of P on the native own-zero subspace and on this fixed-singleton slice, not
just one locally favorable cap branch. No strategic claim about this control
table is needed or made. The table is solely an exact polynomial-identity
control. For context, Gamma has determinant 7345 and strictly positive
inverse column (777,308,189,558)/7345; the construction is compatible with
that existing raw matrix frontier.

## 6. Why this is an arbitrary-law certificate obstruction

The theorem quantifies over all roots and all full-box states. The short
reset word is used only to expose the analytic obstruction to that universal
inequality. It is not an enumeration of candidate equilibrium controllers.

For an arbitrary actual independent law, moving each player's finite mass
after date T to Never changes its total variation by a quantity tending to
zero. Coupling bounds prescribed payoff and EVERY unilateral response change
by the same reward-bound times that probability. Suprema preserve the cap
bound. The original N coordinates also converge. Thus finite Never-ended
words are dense in the actual augmented semantic carrier. A continuous
full-box minorant monotone under every root and positive at the Never seed
would indeed certify a positive lower bound against ALL independent laws.
Parts 2--3 show that the analytic version of that valid grammar fails
generically, before any coefficient search or choice of degree.

This does not invalidate the checked controller--tester barrier duality.
Its greatest barrier is only upper semicontinuous in the interface and is
known to be Lipschitz by the separate nonexpansive-prefix argument. Such a
function may have the required flat open region and change elsewhere.
Nor does this concern the existing polynomial FORWARD separator on the
annotated approximate-Nash relation: its drift contract is different.

Most importantly, a semialgebraic invariant-set certificate requires only
T_q(C) subset C for points IN C. It may exclude off-carrier diagonal points.
There need not be a globally monotone polynomial whose superlevel set is C.
The proof above cannot replace that weaker condition by the global one.
Restricted invariant sets and nonsmooth piecewise function barriers remain
possible search grammars; no producer for either is obtained here.

## 7. Prior work and inspected sources

[The quadratic reset-rank note](CODEX_FRECHET_CYCLE__QUADRATIC_FULL_BOX_BARRIER_RESET_RANK_TEST.md)
uses affine spanning of finitely many reset points and a quadratic maximum
argument for a particular reward family. The present open-image argument
excludes ALL analytic degrees, needs neither a Hessian sign nor a quadratic
ansatz, and allows arbitrary original-N dependence. The
[weighted-debt affine no-go](CODEX_HAHN__WEIGHTED_DEBT_AFFINE_BARRIER_NOGO.md)
and [barrier Lipschitz note](CODEX_SPINOZA__TARGET_FREE_BARRIER_LIPSCHITZ_AND_CAP_SEGMENT_VARIATION.md)
were also inspected. A bounded search found no existing reset-interior or
all-analytic consequence; no exhaustive priority claim is made.

Exact declaration inspections were:

- `quittingTerminalSemanticPrefix`
  (`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`);
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime`
  (`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`);
- `quittingControllerTesterFunctionBarrier_bellman` and
  `quittingControllerTesterValue_functionBarrierDuality`
  (`UniformEquilibrium/Quitting/ControllerTester/FunctionBarrierDuality.lean`);
- `QuittingControllerClosedInvariantBarrier` and its
  `carrier_subset` theorem
  (`UniformEquilibrium/Quitting/ControllerTester/BarrierDuality.lean`);
- `quittingControllerFiniteWordEval_mem_carrier`
  (`UniformEquilibrium/Quitting/ControllerTester/FiniteWordValue.lean`).

No Lean command was run. The exact algebraic checker is
[CODEX_JOINT_CAP_PROBE__GENERIC_ANALYTIC_GLOBAL_BARRIER_NOGO_CHECK.py](../experiments/CODEX_JOINT_CAP_PROBE__GENERIC_ANALYTIC_GLOBAL_BARRIER_NOGO_CHECK.py).
Run it from the repository root with:

    python math/experiments/CODEX_JOINT_CAP_PROBE__GENERIC_ANALYTIC_GLOBAL_BARRIER_NOGO_CHECK.py

The remaining conjecture-facing question is whether a restricted invariant
set can be produced from a genuine candidate, or whether its boundary
constraints force a zero-debt absorbing point. Enlarging the degree of one
globally monotone polynomial is generically ruled out by this theorem.
