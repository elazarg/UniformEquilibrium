# Finite-calendar reward-table tests for payoff-exclusion selectors

Author: CODEX_FRECHET_CYCLE.

Status: complete ordinary-mathematical proposed adapter, not Lean-checked or
independently reviewed. No export is made. The payoff realization dependency
is proved below, not assumed from an unreviewed note. The actual-selector
dependencies are the frozen, independently reviewed packets linked in
Section 5. No cap-preserving compression is claimed.

## 1. Exact output and finite data

Fix four players I={0,1,2,3}. Every nonempty quitting coalition S pays
r(S)∈ℝ⁴; preabsorption and all-Never pay zero. Write s_i=r_i({i}) and fix
M>0 bounding the absolute values of the sixty reward entries. All players
and unilateral deviators may use arbitrary behavioral strategies with
independent private randomization. Equivalently, on the unique live history
they use independent laws on ℕ∪{∞}, where ∞ means Never. No public mixture
or correlated selection is available.

For an actual profile p, let U(p) be its prescribed terminal payoff. The
three hypotheses to be recognized are exactly those in the frozen selector:

- PD: ∃κ>0, every finite word p has min_i(U_i(p)−s_i)≤−κ.
- GE: ∃β<1, every finite word p admits a probability vector w with
  max_i w_i≤β and Σ_i w_i(U_i(p)−s_i)≤0.
- WE_J: fixed nonempty J⊆I has s_i≥0 for i∈J, and every finite word p
  has U_i(p)≤s_i for some i∈J. Singletons outside J may have either sign.

A finite word consists of finitely many independent product rows followed
by all-Never. A fixed prescribed collection of admissible GE weights can
only strengthen its hypothesis: allowing the full capped simplex gives
exactly the existential class above, because that full simplex itself is
one permissible collection.

The result below replaces all finite-word quantifiers by the explicit
twenty-date polynomial predicates (P), (G), and (W). These are equivalent
tests of the same hypotheses, not new sufficient relaxations. Their
accepted tables inherit actual finite-law selection against every complete
behavioral deviation, and a fixed uniform-equilibrium payoff, from the
frozen consumers. The equilibrium words themselves need not have twenty
dates. Rational tables admit exact decision of these three predicates in
principle by finite real quantifier elimination; no engine is implemented.

## 2. Payoff realization on one fixed finite calendar

We prove the needed dependency for n≥1 players, with K=n(n+1). Put

    C_r={U(p): p is any actual independent stopping-law profile}.

Theorem 2.1. Every point of closure(C_r) is the payoff of one actual profile
whose finite stopping dates lie in {0,…,K−1}, with Never also allowed.
Each player's realizing marginal can additionally have at most n+1 support
actions, counting Never. Thus C_r itself is compact and is the image of one
fixed finite product simplex. For Fin4, K=20.

Proof. Censor each original marginal after a cutoff, moving only its finite
tail mass to Never. That changed mass tends to zero even when the original
Never mass is positive. Independent coupling bounds the change of each
bounded payoff by 2M times the sum of these finite tail masses. Therefore
finite-law actual payoffs approximate all actual payoffs; by choosing a
cutoff separately for each member of a convergent sequence they approximate
every point of closure(C_r).

For one finite-law product profile, hold all but player i fixed. Its WHOLE
payoff vector is a convex combination of the vectors obtained when player
i instead uses one of its currently supported pure dates or Never. There
are finitely many such vectors in ℝⁿ. A combination with more than n+1
positive weights has an affine dependence: move weights along that
dependence, preserving their sum and vector, until one first becomes zero.
Iteration gives at most n+1 currently supported actions. This operation
preserves all n prescribed payoffs, not only the mixer's own payoff.

Do this successively for all n players against their CURRENT opponents.
Later operations do not enlarge any earlier support. Every operation
preserves the same whole vector, and there is one independent product
profile throughout. The union of its finite support dates has size at most
n(n+1). Apply one increasing rank map from that union to {0,…,K−1}, fixing
Never, to every marginal. It preserves all comparisons and ties among
realized clocks, so it preserves the first quitting coalition pointwise.
This transforms each marginal separately and preserves independence.

The resulting profiles all lie in one fixed finite product simplex. Its
subset with marginal support size at most n+1 is a finite union of closed
products of simplex faces, hence compact. The prescribed-payoff map is a
polynomial on this space. A subsequential limit of the compressed finite
approximants therefore realizes the desired closure point exactly, retaining
the support bound. Conversely every such finite profile is actual. QED.

This independently verifies the payoff part of
[TARSKI's realization note](CODEX_TARSKI_PREMIUM__FINITE_CALENDAR_PRESCRIBED_OUTCOME_REALIZATION.md)
and Theorem 2.1 of my earlier
[payoff-carrier note](CODEX_FRECHET_CYCLE__ACTUAL_PAYOFF_CARRIER_POTENTIAL_LOCALIZATION.md).
It uses neither that note's potential arguments nor the stronger full-law
realization bound. No cap coordinate enters the finite observables.

## 3. Explicit polynomial data and exact predicates

Return to Fin4. Use eighty-four real variables x_i,t, with i∈I and
t∈{0,…,19,∞}. Define the product-simplex condition

    Δ(x):  x_i,t≥0 for every i,t, and Σ_t x_i,t=1 for every i.

For each nonempty S⊆I put

    P_S(x)=Σ_(t=0)^19 [∏_(i∈S)x_i,t]
                         [∏_(j∉S)(x_j,∞+Σ_(u=t+1)^19 x_j,u)],
    P_∅(x)=∏_i x_i,∞,
    V_i(r,x)=Σ_(S≠∅) P_S(x)r_i(S),
    A_i(r,x)=V_i(r,x)−s_i.

The P_S are degree-four polynomials in x. Their events are the disjoint
first-quitting-coalition events, so Σ_S P_S=1. The functions V_i are
polynomial jointly in the raw table and x, and linear in the table for fixed
x. Theorem 2.1 says C_r={V(r,x): Δ(x)} EXACTLY.

Every x is an executable twenty-row product word: at live date t use hazard
x_i,t/(x_i,∞+Σ_(u≥t)x_i,u) when the denominator is positive, and zero
otherwise. Subsequent rows are all-Continue. Conversely any finite product
word yields independent finite clock laws by multiplying the preceding
survival probabilities. Thus the finite-calendar image is contained in the
finite-word image, and Theorem 2.1 gives equality with the payoff image of
ALL finite words and even all unrestricted actual profiles.

### Strict deficit

Define the raw-table predicate

    (P)  there is NO x satisfying Δ(x) and A_i(r,x)≥0 for every i.

Then (P) is equivalent to PD. For the nontrivial direction, the continuous
function f(x)=min_i A_i(r,x) is strictly negative at every x∈Δ by (P).
Compactness gives max_Δ f<0; take κ=−max_Δ f>0. The resulting bound applies
to every actual profile by exact payoff realization. The converse follows
because a nonnegative surplus vector contradicts every positive κ.

For a SUPPLIED κ>0, the exact predicate is instead

    ∀x, Δ(x) ⇒ [∨_i A_i(r,x)≤−κ].                       (Pκ)

Using A_i>0 in the forbidden system (P) would characterize only weak
exclusion, and is not a valid strict-deficit test.

### Weak subset exclusion

For supplied nonempty J define

    (W_J)  [s_i≥0 for all i∈J], and there is NO x with
           Δ(x) and A_i(r,x)>0 for every i∈J.

This is equivalent to WE_J by exact payoff realization, without a margin or
closure approximation. If the problem is to recognize the existence of a
witnessing subset, it suffices to take the maximal allowed set

    J₊={i:s_i≥0}.

The existential subset version holds iff J₊ is nonempty and (W_J₊) holds:
enlarging a witnessing subset preserves its disjunction. Equivalently one
may use the finite disjunction of (W_J) over the fifteen nonempty subsets.

### Nonconcentrated group exclusion

For λ∈(0,1/2] define twelve ordered-pair polynomials

    L_ij(r,x,λ)=(1−λ)A_i(r,x)+λ A_j(r,x),   i≠j.

The exact raw-table predicate is

    (G)  ∃λ, 0<λ≤1/2 and
         ∀x, Δ(x) ⇒ [∨_(i≠j) L_ij(r,x,λ)≤0].         (G)

Equivalently, some such λ makes the finite polynomial system
Δ(x), L_ij(r,x,λ)>0 for EVERY ordered pair i≠j infeasible.

Proof of equivalence to GE. Any admissible β can be enlarged to
β'=max(β,1/2)<1. Put λ=1−β'. For any surplus vector a, let i index its
smallest coordinate and j a smallest coordinate outside i. For every
probability weight with each coordinate at most β',

    Σ_k w_k a_k ≥ w_i a_i+(1−w_i)a_j
                ≥ β'a_i+(1−β')a_j.

Equality is attained by the admissible weight β'e_i+(1−β')e_j. Hence the
minimum over the capped simplex equals min_(i≠j)[(1−λ)a_i+λa_j]. GE
therefore implies (G). Conversely a pair witnessing (G) gives exactly an
admissible probability weight with β=1−λ<1. This holds profile by profile,
with one uniform λ but without requiring one fixed pair. QED.

The quantifier order ∃λ∀x is essential. Replacing it by ∀x∃λ would not
supply the frozen selector's uniform nonconcentration parameter. Pairs must
be distinct; i=j would silently allow concentrated weights.

## 4. Semialgebraic recognition and finite certificate interface

For the sixty raw reward variables, (P), (W_J), and (G) are explicit
first-order formulas over the reals using the finite polynomial family
above. Real quantifier elimination therefore makes their truth sets
semialgebraic, and decides membership for rational or real-algebraic input
tables in principle. This is an application of the real closed field
decision theorem, not a claimed new algorithm or an efficiency result.
No expanded quantifier-free formula or implemented solver is claimed here.
For arbitrary unencoded real input the statements remain exact mathematical
equivalences, not computational promises.

The interface supplies all quantitative parameters needed by the consumers:

- If (P) is accepted for a rational table, some rational κ>0 satisfies
  (Pκ). After recognizing (P), testing κ=1/k for k=1,2,… terminates.
- If (G) is accepted, some rational λ∈(0,1/2] works. Indeed the minimum
  pair value is a_(1)+λ(a_(2)−a_(1)), which is nondecreasing in λ.
  Any smaller positive λ remains valid. After recognizing (G), testing
  λ=1/k for k=2,3,… terminates. Set β=1−λ.
- (W_J) requires no positive separation margin. Equality cases are accepted
  exactly; finite sampling alone is not a decision procedure for this test.
- A rational M larger than every absolute reward is immediate. Positive
  error tolerances can likewise be taken rational.

Every individual test in these searches is the finite real-algebraic
predicate just displayed. Rejection of (P) has an actual twenty-date
witness with every surplus nonnegative; rejection of (W_J)'s exclusion
clause has one with every surplus in J strictly positive. For rational
tables real-algebraic witnesses can be chosen in these semialgebraic sets.
Their laws are genuine independent laws. Rejecting (G), by contrast, need
not give ONE profile defeating every λ: its exact negation retains
∀λ∃x. No contrary single-witness assertion is made.

## 5. Actual-data adapter and existing consumers

Apply the complete, frozen
[payoff-exclusion selector](../exports/PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS.md).
Its hypotheses are precisely the all-finite-word statements established in
Section 3. It computes each new word's complete response caps afresh, so
does not need the bounded realization to preserve any cap.

For each accepted (P), (G), or (W_J), and each ε>0, that packet gives one
actual finite word p with

    Σ_i [sup_(all behavioral deviations τ_i) U_i(p[ i←τ_i ])−U_i(p)] < ε.

The deviations include every finite date, unbounded stopping laws, and
Never. Rational tables and supplied rational bounds give terminating
rational-word constructions: geometric debt decay for PD, reciprocal decay
for GE, and the stated table-uniform O(ε⁻² log(1/ε)) weak construction
(with its explicit n,M dependence). The packet also proves the terminal to
uniform-payoff passage; the target payoff is fixed before the equilibrium
error tends to zero.

Under (P) AND s_i≥0 for every player, its stronger consumer gives one
infinite profile that is exact terminal Nash at every suffix, and has the
stated uniform-payoff property. The sign assumption is not needed for the
finite PD or GE selectors. WE requires only the signs on its witnessing J.
No exact terminal Nash conclusion is claimed from (G) or (W_J) alone.

When every singleton is nonnegative, (W_I) may also feed the frozen
[cap-threshold selector](../exports/FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION.md),
including its unblocked-column exit and its different fixed-table bounds.
This is a choice of existing consumer, not an additional premise.

There is a broader QUALITATIVE Fin4 consequence already supplied by current
Lean mathematics. Even without sign assumptions, if some nonempty J has
no actual payoff strictly above s on J, the current strict-minimum plateau
theorem contradicts a hypothetical absence of uniform-equilibrium payoff.
Indeed that theorem supplies a semantic-carrier point whose prescribed
coordinates are strictly above every singleton. The carrier is the closure
of actual (U,B) pairs; projecting an approximating sequence puts that payoff
in closure(C_r)=C_r. Theorem 2.1 gives an actual bounded-calendar payoff
witness, contradicting the test. Only the payoff projection is realized;
the plateau's caps are not assigned to the realizing profile. This
qualitative implication was already available by approximating its strict
gap. It is not a new unrestricted selector with signed witnessing owners.

## 6. Boundary tests and exact scope comparisons

1. All-Never is x_i,∞=1; all prescribed payoffs are zero. A pure coalition
   at date zero is represented literally. The formulas keep these cases
   distinct, including the pure full-coalition tie.

2. PD is genuinely strict. Set s_i=1; at singleton {i} pay i one and
   everyone else minus one, and at every other nonempty coalition pay
   everyone minus one. Every actual payoff has coordinate sum at most zero,
   so min_i(U_i−1)≤−1 and PD holds with κ=1. In contrast, for the identically
   zero table PD fails at all-Never, while GE and every WE_J hold exactly
   on the equality boundary.

3. WE need not imply GE. Set r_0(S)=1 for every nonempty S. For j≠0 set
   r_j({0})=1 and r_j(S)=0 for every other nonempty S. Then s=(1,0,0,0)
   and U_0≤1 always, so WE_{0} holds. Pure {0} has surplus (0,1,1,1):
   every weight with max coordinate≤β<1 gives surplus ≥1−β>0.
   Thus GE and PD fail. This is a boundary example with an easy equilibrium,
   not an additional difficult game class.

4. GE properly goes beyond PD and the existing fixed nonnegative-weight
   reward-convex-hull criterion. Let A={0,1}, B={2,3}, with each player's
   partner in its pair. Set s_i=1 and

       r(A)=(2,2,1,1),       r(B)=(1,1,2,2).

   At singleton {i}, pay i one, its partner zero, and each outsider 1/2.
   At every remaining nonempty coalition pay every player 1/2. Let x,y be
   the actual terminal masses of A,B, ν the Never mass, and z=1−x−y−ν.
   The two group-average surpluses are x−z/2−ν and y−z/2−ν.

   Independence gives √x+√y≤1: compare clocks 0 versus 2 and independently
   1 versus 3. If their strict-order probabilities are a,b and a',b', then
   x≤aa', y≤bb', a+b≤1, a'+b'≤1; Cauchy–Schwarz proves the bound. If
   x≤y, put t=√x≤1/2. Then 3x+y≤3t²+(1−t)²≤1, so the first group
   surplus is (3x+y−1−ν)/2≤0. The other ordering uses the second group.
   This proves GE with β=1/2. Pure A has surplus (1,1,0,0), refuting PD.
   The half-A/half-B CORRELATED lottery has strictly positive surplus in
   every coordinate, refuting any nonzero nonnegative linear separator of
   the full reward convex hull. That lottery is not asserted to be actual.
   Pure A also fails the own-singleton product-low endpoint criterion:
   its two active players have Quit payoff 2>s_i. The unit-normalized
   source predicate is a different condition and is not identified with
   that own-singleton test here. This table itself has an easy pure A Nash
   equilibrium; failure of those tests is not a claim of an unsolved class.

5. PD implies GE for Fin4: if min_i a_i≤−κ and |a_i|≤2M, choose
   0<λ≤min(1/2,κ/(2M+κ)); weight 1−λ on a deficit coordinate and λ
   on any distinct coordinate. The weighted surplus is at most zero.
   If all singletons are nonnegative, GE in turn implies WE_I. Signed
   witnessing subsets must still satisfy their separate WE sign premise.

6. These tests do not decide UE existence. For example, pay every player
   one at its own singleton, two at the full coalition, and zero in all
   otherwise unspecified entries. Pure full quitting has surplus (1,1,1,1),
   so PD, GE and every WE_J fail; nevertheless that pure profile is exact
   terminal Nash because a sole player continuing instead receives zero.

7. Prescribed payoff preservation cannot be used to transport caps. In
   two players set r_0({1})=1 and every other reward entry zero. The pure
   profiles (0,1) and (0,∞) have the same terminal coalition {0} and payoff
   zero; player 0's response cap is respectively one and zero. Two inert
   Never players embed this test in Fin4. The adapter uses no such transfer.

## 7. Source correspondence, delta, and handoff

The bounded source audit inspected:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `quittingBehaviorStoppingLaw_finiteStoppingLawMixture` and
  `quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect` in
  `UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean`:
  the latter explicitly covers every observer, supporting whole-vector
  affine replacement rather than only the mixer's own payoff;
- `quittingTerminalSemanticCarrier` and
  `exists_terminalProfile_sequence_tendsto_semanticPair` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff`
  in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`;
- `exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`:
  its fixed weight has two positive coordinates and bounds every terminal
  row, including Never. Normalize that weight to see it is a special GE
  certificate; Section 6 gives exact strict separation of the conditions;
- the frozen selector's complete source correspondence, including the
  terminal all-errors uniform-payoff consumer and its actual-law adapters.

The realization proof has two independent conference derivations linked in
Section 2. Finite affine support reduction and real quantifier elimination
are classical ingredients. The new connection is their exact attachment to
PD/GE/WE and the existing actual producers: an infinite collection of
finite-word hypotheses becomes a fixed-dimensional raw-table recognition
problem, with quantitative κ or β recoverable where needed.

No new qualitative class is claimed beyond the corresponding existing
payoff-exclusion implications; no global comparison against every normal-core,
non-Q, odd/even, or projective criterion is attempted. The evidence above
separates specific named conditions only. No recognized table is asserted
to lie outside all other known equilibrium results.

A Lean handoff can first formalize the fixed-calendar payoff realization,
then the polynomial first-outcome map and the three equivalences, and finally
compose them with formalized versions of the frozen selectors. Recognition
does not require a cap representation. No generic QE implementation is
needed to state or use the mathematical adapter; decision procedures can
remain an external classical consequence for encoded coefficients.

Requested independent check: falsify the uniform capped-weight reduction
or the exact image equality, especially at zero masses, Never atoms, and
weak-equality boundaries. Those are the only new interfaces to the already
reviewed selector; no optimization of calendar size or constants is proposed.
