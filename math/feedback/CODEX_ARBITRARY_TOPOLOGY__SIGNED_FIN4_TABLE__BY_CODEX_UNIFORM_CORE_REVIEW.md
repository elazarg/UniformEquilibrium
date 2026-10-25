# Review of the signed Fin4 stationary and sure-root exclusions

Reviewer: CODEX_UNIFORM_CORE_REVIEW.

**Mathematical PASS.** No unresolved mathematical objection in the complete
stationary exclusion, positive stationary regret floor, or exclusion of
exact Nash profiles with a bounded proper clock. This is an independent
ordinary-mathematical and exact-code audit, not a Lean check, an export
approval, or an exclusion of unrestricted nonstationary equilibria.

Reviewed artifacts:

- [Complete table and proof](../notes/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_TABLE.md),
  SHA256 `1f3815857c0df1aab93a929234e15663955f53e2293bcde0589f930c3d0f0584`.
- [Retained exact checker](../experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py),
  SHA256 `0c3dd850b01c1e3fe2caf7ca5b47ea07df492ea2f5943f5a691d025659ab3431`.

## 1. Table, singleton screens and observer margins

The printed coalition table agrees entry by entry with the checker. The
original rewards are 1+Z only at nonempty absorption; live play and AllNever
remain zero. This distinction is retained in the solo and origin arguments.

I independently recomputed the singleton determinant, all principal minors
of sizes two and three, and the positive inverse column. The R0 argument is
valid: an alleged nonzero complementary vector has an invertible principal
matrix on any support of size at least two, while every singleton support
has a negative exterior entry. No implication from these screens to all
arbitrary-counterexample hypotheses is claimed.

I also independently computed the four capacities by checking endpoints and
all pairwise line intersections. They are exactly 1, 1/5, 3/29 and 1/7 at
the stated maximizing hazards. The joining-gap arithmetic and its transitive
orientation check. These positive capacities concern attainable observer
margins; they do not themselves supply a whole-game equilibrium.

## 2. The stationary response menu

If at least two hazards are positive, each deviator faces opponent
absorption with probability one. Therefore the absorbing row shift adds
exactly one to every prescribed value and every response. In native units,
Never is P_i/(1-H_i), and a deadline t offers

    (1-H_i^t) P_i/(1-H_i) + H_i^t Q_i.

Thus all independent stopping laws, including all behavioral deviations,
are bounded by the Quit0 and Never endpoints. For own hazard strictly
between zero and one, the prescribed value is a convex combination with
both endpoint weights positive. The required conditions are consequently
F_i<=0 at zero, F_i=0 in the interior and F_i>=0 at one, with
F_i=(1-H_i)Q_i-P_i exactly as implemented.

For each solo owner, the selected observer faces proper opponents and has
the stated strictly positive Quit0-minus-Never gap. This excludes solo
profiles uniformly as their positive hazard tends to zero. AllNever is
excluded in original coordinates by the own-singleton payoff one.

## 3. Exact finite coverage and code audit

I inspected the complete checker and ran its documented command. It reports
all 80 nonzero support patterns excluded, with 898 visited nodes. I also
performed a separate exact reconstruction: the polynomials were rebuilt
from the printed coalition vectors, and each box bound was recomputed by
direct affine substitution into the original power polynomials followed by
rational Bernstein conversion. This second calculation did not use the
retained restriction, inversion or integer-subdivision routines. It obtained
the same 80 exclusions and 898 nodes, including 213 for the full interior.

The relevant code invariants check:

- Every coordinate is classified as zero, one or interior; only the all-zero
  pattern is omitted. Closed cubes enlarge the interior domains, which is
  legitimate for exclusion. Pure cases and solo interiors have separate
  exact sign certificates.
- The polynomials are obtained directly from the forced-Quit and passive
  coalition probabilities. Their individual variable degrees are at most
  two. Restriction substitutes fixed zero or one correctly.
- Inverse-principal-matrix combinations are added only as consequences of
  active equality rows. They cannot remove a valid solution. All relevant
  principal matrices are invertible.
- Tensor Bernstein coefficients bound the polynomial by convexity. Only
  strictly inconsistent bounds discard boxes; equality at a bound does not.
  Clearing a common positive denominator preserves every sign.
- The integer subdivision triples are four times the exact coefficients on
  each closed half. The halves cover the parent box, and repeated positive
  scaling is harmless. Unresolved depth or node limits fail explicitly.

For patterns without a sure coordinate, the checker verifies the zero
constant and exact linear term -Gamma_SS q before invoking the origin
bound. Every remaining monomial has total degree at least two, hence
absolute value at most t^2 for t=max q_i<=1. Multiplying by the inverse gives

    t <= K t^2.

The discarded origin boxes satisfy t<=2^(-E)<1/K. Their only possible common
zero is the origin, which is outside the actual interior-support pattern.
The zero-K branch is also sound. I independently obtained the full-support
constant K=159656/25 and its valid exponent E=13. No floating computation,
solver status or saved search output is used as an exclusion premise.

## 4. Sure roots over arbitrary actual continuation caps

The continuation lower bound uses the original literal Never response,
including AllNever. Subtracting one gives a convex average of passive Z_i(A)
values and -1, not zero. Hence every actual cap satisfies B_i-1>=L_i with
L=(-12,-8,-10,-12), without properness or optimality of the continuation.
I independently recomputed these four minima from the printed table.

The original Quit offer is 1+Q_i. Continuing at the root and then responding
optimally offers

    (1-H_i)+P_i+H_i B_i = 1+P_i+H_i(B_i-1).

The Quit-minus-Continue gap is Delta_i-H_i(B_i-1), with Delta_i=Q_i-P_i.
This is distinct from the stationary polynomial F_i. Supremal continuation
caps suffice: if the bound failed, a sufficiently close finite-error response
would already contradict exact root optimality.

If p quits surely, every other player's H_i vanishes. Those players' signs
are unaffected by any continuation replacement. For p itself, lowering
B_p-1 to L_p only increases the gap, preserving the required nonnegative
sign. With two or more sure owners every H_i vanishes. Thus the displayed
sign conditions for J_i=Delta_i-H_i L_i are necessary for every actual sure
Nash root; no assumption that the artificial lower-cap vector is realizable
is made or needed.

I independently rebuilt all four J_i from the printed table and checked
the added checker mode. The 65 patterns are exactly those with at least one
fixed-one coordinate. The same direct-affine, rational Bernstein audit
reproduced all 325 nodes and excluded every pattern. There is no origin
pruning and no solo-interior shortcut in this mode. Although Gamma need not
be the linear part of J, its inverse still gives valid linear combinations
of active equalities. The unchanged stationary mode also reproduces its
original 898-node result.

The finite-calendar adapter is sound. A bounded proper clock has a finite
last possible date, so some root no later than that date has a sure owner.
Choose the earliest sure root; every previous all-Continue event then has
positive probability, so this root is reached with positive probability.
Global exact Nash implies the required local response comparisons there.
In particular, a sure owner's deviation may Continue and then exploit the
actual off-path opponents; it is not restricted to the prescribed calendar.
The lower-cap argument permits arbitrary such continuation play.

Consequently an exact terminal Nash profile cannot have even one bounded
proper clock, irrespective of the other clocks' support sizes. Every
absorbing finite-calendar independent profile has a bounded proper clock:
otherwise every player has positive Never mass, giving positive AllNever
probability by independence. Thus the claimed exact finite-calendar
exclusion follows. The final added bounded-clock sentence is the direct
stronger consequence of the same proof.

This supplies no positive global regret floor over finite calendars. Their
first sure root can become arbitrarily unlikely as the calendar varies;
a strict local improvement need not give a fixed ex ante improvement.

## 5. The positive stationary regret floor

Absence of an exact stationary equilibrium alone would not establish a
uniform regret floor. The proof addresses every discontinuity explicitly.

At a nonzero limit with two active owners, all players face proper opponents;
prescribed payoffs and both response endpoints are continuous. Vanishing
regret therefore gives an exact stationary equilibrium, already excluded.
At a solo limit, the selected observer's prescribed value tends to its
Never value and its positive Quit0 advantage persists. No continuity of
the solo owner's Never payoff is needed.

At a zero limit, write s=sum q_i and pass to alpha=q/s. The first-order
absorption expansion yields U_i -> 1+(Gamma alpha)_i, while Quit0 -> 1.
Thus Gamma alpha>=0. When alpha_i<1, the opponent absorption rate is of
order s(1-alpha_i), so Never converges to
1+(Gamma alpha)_i/(1-alpha_i). Comparing it with U_i gives
alpha_i(Gamma alpha)_i<=0 and hence equality. At alpha_i=1 the zero diagonal
gives equality directly. The resulting nonzero complementary vector
contradicts R0. Zero profiles themselves have regret at least one.

This proves a positive terminal exploitability floor throughout the
stationary class. For any fixed stationary profile a profitable terminal
deviation remains profitable at sufficiently long finite horizons, so
stationary profiles also cannot provide uniform approximate equilibria at
arbitrarily small error. The compactness argument supplies an existential
floor; it does not calculate a numerical value.

## 6. Scope and semantic checks

I inspected `quittingUniformEquilibriumPayoffConjecture` in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean` and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The latter requires approximate terminal Nash profiles without a stationary
restriction. The stationary and bounded-proper-clock exclusions do not
settle the uniform-equilibrium status of the printed table. They do not
exclude periodic profiles with no sure root, approximate finite-calendar
equilibria, or unrestricted behavioral approximate equilibria.

No author note was edited and no Lean source was changed or built.
