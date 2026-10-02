# Simon–Zame sharing rules at the single-pivot boundary

Author: CODEX_TARSKI_PREMIUM.

Status: this ONE native-theorem application is stopped as a direct
original-law producer. Its hypotheses hold for an enlarged payoff
correspondence, not for the original fixed-zero-Never game. The theorem
can absorb the known finite-Nash escape by changing the payoff at
infinity; it does not select original approximate equilibria. The exact
original-regret calculation below uses every finite response and Never.
Ordinary mathematics, no independent review, Lean claim, or export.

## 1. Primary theorem and the distinction from the stopped security routes

The selected primary result is the unnumbered theorem in Section 2,
printed page 865, of Simon and Zame, *Discontinuous Games and Endogenous
Sharing Rules*, Econometrica 58 (1990), 861–872
([original paper](https://kylewoodward.com/blog-data/pdfs/references/simon%2Bzame-econometrica-journal-of-the-econometric-society-1990A.pdf)).
It assumes compact metric pure-strategy spaces and a bounded upper
hemicontinuous payoff correspondence with nonempty compact convex values.
It gives a Borel selection and an independent mixed-strategy Nash
equilibrium for that selection. It does not prescribe the selection.

Section 3, Steps 1–3, permits finite strategy nets and payoff selections,
then takes strategy and payoff-measure limits. The introduction on printed
page 864 expressly distinguishes this direction from approximating a
selected limiting solution by finite approximate equilibria; it leaves
that converse unresolved there. This is a statement about the 1990 paper,
not a claim about the current literature's complete state.

This is not Reny better-reply security, marginal continuity, or approximate
better-reply security. The previous canonical failures of those hypotheses
are not used to falsify Simon–Zame. The changed conclusion is checked directly.

## 2. Exact correspondence on the original pure clocks

Fix a bounded raw Fin4 table with own singletons s=(1,0,0,0), independent
stopping laws on K=ℕ∪{∞}, and original all-Never reward zero. Give K its
one-point-compactification topology. Finite dates are isolated and n→∞.
Let f(t) be the original pure stopping-time payoff vector.

At every tuple except (∞,∞,∞,∞), f is locally constant: the finite first
stopping date and its coalition can be fixed on a product neighborhood.
The only pure-profile discontinuity is therefore all-Never. Every terminal
reward r(S) is a limit there: put the players in S at date n and the others
at ∞. The original value zero is also present at that point itself.

Put C=conv({0}∪{r(S):S nonempty}) and define

    Q(t)={f(t)}                  if t≠(∞,∞,∞,∞),
    Q(∞,∞,∞,∞)=C.                                         (1)

This is bounded, nonempty, compact convex-valued, and upper hemicontinuous.
Away from all-Never it is locally constant. At all-Never, every nearby
payoff lies in the fixed compact set C. All selections are measurable here:
K⁴ is countable with Borel singletons. Thus the theorem applies.

It cannot be applied while requiring Q(∞,∞,∞,∞)={0}. The pure sequence
(n,∞,∞,∞) has pivot payoff one and converges to all-Never, directly
violating upper hemicontinuity of that fixed selection. This failure is
already forced by the canonical singleton, irrespective of no-UE premises.

Every selection from (1) changes exactly ONE pure outcome: it replaces
zero Never by some vector v∈C. In particular the theorem does not add a
new finite pivot response or price its newly induced joining responses.
All finite responses are already present in its infinite game; their
limiting boundary payoff is allowed to change instead.

The zero is included in C so the ORIGINAL payoff function is itself an
allowed selection for every finite approximation. If one instead takes
the convex completion only from the dense domain of terminating pure
tuples, its boundary set is conv{r(S)}. That smaller construction still
changes the prescribed Never outcome and does not repair the conclusion.

## 3. Full original regret at any resulting equilibrium

Let μ be ANY exact equilibrium of the selected game with Never reward v.
Its marginal Never masses and their products are

    z_i=μ_i(∞),       Z=∏_i z_i,       D_i=∏_(j≠i)z_j.

Write U_i for its ORIGINAL prescribed payoff, W_i for its ORIGINAL Never
response, and H_i=sup_(finite t)V_i(t) for its ORIGINAL finite-response
cap. Nonnegative own singletons give

    lim_(t→∞)V_i(t)=W_i+D_i s_i≥W_i,
    B_i=H_i.                                              (2)

Thus neither Never nor any unlisted deadline is discarded. The selected
game's payoff and response values are exactly

    Ũ_i=U_i+Z v_i,
    Ṽ_i(t)=V_i(t) for finite t,
    Ṽ_i(∞)=W_i+D_i v_i.                                  (3)

Its full Nash inequalities imply

    0≤d_i:=B_i−U_i≤Z v_i.                                (4)

If Z=0, (4) already proves exact ORIGINAL terminal Nash, including a
possible deviator who restores the all-Never event. Equation (2), rather
than the prescribed probability Z alone, is what controls that deviation.

If Z>0, every z_i>0, so the supported Never action attains Ũ_i. When
z_i<1 there is also a positively used finite date, which attains Ũ_i;
therefore

    H_i=Ũ_i=W_i+D_i v_i,
    d_i=Z v_i,              v_i≥s_i.                      (5)

When z_i=1, U_i=W_i and (2) instead gives

    d_i≥D_i s_i=Z s_i.                                   (6)

Since v belongs to the reward hull, |v_i|≤M for a common reward bound M≥1.
Applying (4)–(6) to the pivot yields the exact useful comparison

    Z≤E_original(μ)≤M Z.                                 (7)

For positive Z, (4) also forces v_i≥0 for every player. The upper bound
in (7) involves JOINT Never mass, not merely pivot-deleted Never mass.
This is an identity/bound for supplied solutions of the selected infinite
game, not a theorem producing solutions with small Z.

Thus the needed additional selection is concrete: obtain Simon–Zame
solutions with Z→0. Neither its existence conclusion nor its compactness
of solution outcomes asserts this. Appending an external small-regret
tail, demanding a particular v, or adding that selection as a theorem
field would simply reintroduce the missing original source problem.

## 4. Exact test on the known bad canonical finite-Nash sequence

Use the already solved VANISH table, with cyclic predecessor/successor
among players 1,2,3:

    r_0(S)=1 if 0∈S, and 2 otherwise;
    r_i(S)=0 if i∈S;
           −1 if i∉S and 0∈S;
           2·1_(i⁻∈S)−1_(i⁺∈S) otherwise,  i>0.

In particular r({0,1,2,3})=(1,0,0,0)=:e_0, so e_0∈C without any
convexification or payoff-realization issue.

The complete existing finite-menu classification gives, for EVERY N≥1,
the unique exact Nash law on F_N={0,...,N−1,∞}. All finite mass is at
N−1; put

    a=1−2^(−1/3),       b=a/(1+a).

The pivot quits there with probability b and each nonpivot with probability
a. The ORIGINAL payoff is e_0, and its full ORIGINAL regret is 1/2.
These laws converge weakly to μ*=(δ_∞,δ_∞,δ_∞,δ_∞).

The finite grids F_N are legitimate approximating nets for K. In Step 1
of the Simon–Zame proof choose the original payoff selection, including
zero at all-Never. It belongs to (1). There is no finite-Nash selection
tie to resolve: the preceding source classifies all those finite Nash laws.
The payoff-weighted measures converge to e_0 δ_(∞,∞,∞,∞). Therefore any
resulting sharing rule must take value e_0 at the limiting all-Never point,
which has probability one. A null-set correction cannot change that value.

The resulting solution is fully valid: against all-Never opponents each
finite deviation pays s_i, and prescribed selected Never pays (e_0)_i=s_i.
But in the ORIGINAL game μ* has payoff zero, pivot cap one, and

    Z(μ*)=1,        E_original(μ*)=1.                    (8)

Thus the original-common-menu implementation of this native theorem's
finite approximation proof has a complete, exact escape on the canonical
bad example. It does not turn the finite-menu loss 1/2 into vanishing
original regret; its limiting sharing rule instead validates a different
payoff at infinity.

This does NOT exclude other payoff selections, asymmetric grids, or other
Simon–Zame solutions. VANISH in fact has an exact infinite cyclic ORIGINAL
equilibrium, with proper nonpivot clocks and Z=0, and hence a good solution
of (1). Accordingly the bad solution alone is not called a counterexample
to existential joint reselection. The result is that the chosen theorem
and its tested original-menu construction do not supply that reselection.

## 5. Stopping point and exact source correspondence

The theorem is valid for the enlarged correspondence and inapplicable to
the original fixed-zero-Never payoff correspondence. Its direct original-
approximation interpretation is therefore stopped. The exact relation (7)
does not merit another supplied-small-Z interface or an export. No new
raw-table class, counterexample restriction, or full strategy-class
impossibility has been proved.

The only primary theorem used was the Simon–Zame theorem cited above;
Section 2 and the relevant approximation/selection steps were read in the
original paper, not taken from a secondary theorem summary.

The inspected repository sources and relevant prior notes are:

- `singlePivot_fullExploitability_eq_max_menuExploitability_scalar`, in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`;
- `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`,
  in `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`;
- the complete stopping-law mixture and pure-response-cap correspondence
  in `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`;
- [canonical exact-menu separation](CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md),
  supplying the complete finite Nash classification and the successful
  infinite original equilibrium used only to delimit the falsifier;
- [Reny boundary security](CODEX_TARSKI_PREMIUM__RENY_SECURITY_AT_THE_INFINITY_PAYOFF_FIBER.md),
  [marginal continuity](CODEX_NOETHER_SUPPORT__SINGLE_PIVOT_MARGINAL_CONTINUITY_OBSTRUCTION.md),
  and [approximate security](CODEX_NOETHER_SUPPORT__CANONICAL_APPROXIMATE_SECURITY_COUNTEREXAMPLE.md),
  which concern different hypotheses and do not imply this theorem fails;
- [pivot-boundary homotopy](CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md),
  which modifies only the pivot coordinate in finite games. In contrast,
  (3) is an arbitrary hull-valued Never modification with every infinite-game
  finite response already required by Nash.

No literature survey beyond this single selected theorem, framework
implementation, original reward change, or claim of actual cap continuity
under weak law convergence is made.
