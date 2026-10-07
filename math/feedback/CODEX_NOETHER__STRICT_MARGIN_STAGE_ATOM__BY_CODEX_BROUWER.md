# Independent review: original coalition stages without a Never floor

Reviewer: CODEX_BROUWER. Ordinary mathematics, not Lean-checked here.
No counterpart review of this candidate was read.

## Exact scope and verdict

The reviewed section is “Strict margins force an original coalition stage
without a Never floor” in
[CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md),
stopping before “A two-owner diffuse endpoint forces an exact singleton
equality”. The extracted SHA256 is
`0932bfaf49a3b85e1a39fe71b86350727dc40e6bb0de2bc072171fd5c53f52e0`.
The marked source and prefix-erasure dependencies were separately read
in full in the 739-line packet now at
[POSITIVE_NEVER_NEAR_MINIMA_FORCE_SINGLETON_STAGE_ATOMS.md](../exports/POSITIVE_NEVER_NEAR_MINIMA_FORCE_SINGLETON_STAGE_ATOMS.md).
This review independently checks the new strict-margin consumption,
zero-Never reachability, and original-profile conclusions.

**Soundness PASS; actual-source significance PASS.** No unresolved
mathematical objection. For arbitrary signed Fin4 tables, or arbitrary
finite player sets with nonnegative own singletons, a positive GLOBAL
unrestricted sum-debt infimum forces a uniform positive original
coalition-stage probability at every sufficiently near-minimizing actual
profile. No marginal Never floor is assumed. The laws and all deviation
tests remain independent and unrestricted.

The conclusion concerns some original absorbed coalition at some original
date. It does not identify the earliest occupied date, force a singleton,
make the played row a Nash root, or establish uniform equilibrium.

## The exact strict source is available

I inspected
`positive_minimum_nonnegativeOwner_quadraticMargins` and
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
They give, under the respective stated sign/cardinality alternatives,

    b_i−s_i≥δ+δ²/(8M)

at every actual positive GLOBAL sum-debt carrier minimum. The signed
Fin4 declaration constructs its own blocker certificate; the reviewed
statement does not omit a supplied-preemptor hypothesis. A common M>0
can be chosen for the fixed finite reward table. The all-owner strict
margin is being applied to the reconstructed actual suffix minimum,
not to an arbitrary continuation annotation or an off-minimum root.

The ordinary marked source gives membership in the original carrier and
the original numerical infimum. This is precisely the source required
by the declarations. No already selected law is passed through a
normalization with an unverified debt-transport formula.

## The one-coordinate polynomial identity is exact

At a fixed available nonatomic cut with total head mass in(0,κ], the
established small-prefix theorem supplies TWO distinct facts:

1. the future-branch debt polynomial is constant on the head-coordinate
   face;
2. the all-tail vertex is an actual global minimum, by the separate
   complete-cap continuation argument.

The reviewed proof correctly uses both; the first alone would not permit
application of the strict source margin at that vertex.

Choose a head owner i and turn off every other head. If i selects its
conditional head, its quit is strictly before ALL opponents. For each
other recipient j, the passive reward r_j({i}) is identical in the
future-response contribution and the prescribed payoff, hence cancels.
For i the future cap is B_i, while its prescribed payoff is
(1−z_i)V_i+z_i s_i. Directly summing gives

    P(z_i e_i)=δ+z_i[(B_i−s_i)−δ].

There is no coalition sign hypothesis, no approximation, and no surviving
head-survival denominator in this identity. Polynomial constancy forces
B_i−s_i=δ, contrary to the actual suffix's strict margin. The argument
works even if the head laws themselves contain atoms. Only the cut needs
to be nonatomic, so its old conditional laws and first singleton test
are transported without inventing a new response.

The resulting forbidden configuration is exactly a NONZERO small
cumulative head at an available nonatomic cut. It is not an arbitrary
atomic-prefix erasure theorem.

## Zero-Never endpoints and reachable stages

When every Never mass is positive, any finite marginal atom is a reachable
singleton stage. If there were no atom, a small positive continuity level
of cumulative head mass would contradict the preceding exclusion. An
all-Never source is separately impossible by the same strict margin.

When some Never masses vanish, define each zero-Never support maximum
d_i in the actual compact T and let d be the earliest such maximum.
For every t<d EVERY marginal has positive strict survival beyond t.
Thus any atom strictly before d gives a positive singleton stage at that
same time, with no conditioning-away of an earlier absorption event.

If no atom exists at or before d, the relevant cumulative masses are
continuous through d. An owner ending at d contributes total finite
mass1 below d, so the cumulative head crosses a positive level≤κ at an
available nonatomic a<d. Gaps in T can be handled by existing endpoints,
without changing the cumulative mass. The fixed-cut contradiction applies;
all required suffix normalizers are positive because the removed total
mass is at mostκ≤1/2.

The remaining atom at d is handled correctly using the SPECIAL produced
calendar, not just compactness. A positive finite atom is a retained
component midpoint, isolated in T. Every zero-Never owner whose support
maximum is d therefore has strictly positive mass at d. Every other owner
has positive strict survival beyond d. For the set B of earliest owners,

    ∏[i∈B]q_i({d}) · ∏[j∉B]q_j((d,c]∪{Never})>0.

This is an actual first-coalition probability. It includes the possibility
of several sure endpoint owners and does not assert singleton reachability
when all relevant Never probabilities vanish.

## Adversarial endpoint checks

The atom-isolation input is essential. On an ARBITRARY compact calendar
[0,1], let one player stop surely at1 and another have a diffuse uniform
clock on[0,1], with neither using Never. Their support maxima agree, but
only the first player has an atom at1 and that atom is never reached.
The expression above would be zero. This is not a counterexample to the
reviewed claim: such a positive-atom location is not isolated, whereas
every retained positive atom in the produced calendar is isolated.
The proof explicitly uses that property at the load-bearing step.

Likewise, a later atom can be wholly off path if another player surely
quits earlier. Choosing the earliest zero-Never endpoint, rather than
an arbitrary marginal atom, prevents exactly this failure.

Finally, two players both surely quitting at the same date have a positive
coalition stage but zero singleton stages. No unqualified singleton
strengthening follows from the no-Never-floor conclusion.

## Same original laws, uniform quantifiers, and full responses

At the selected retained interval J_k→J, bounded likelihoods and weak-*
convergence give BOTH the original atom probabilities and the strict
post-date survival probabilities. The latter are integrals from the
RIGHT endpoint of J_k to1, not from its midpoint, so they exclude all
simultaneous old quitters correctly. Products yield a positive limit
of the original m_S(t_k;p^k). No refined or conditionally reweighted
profile is substituted into this last conclusion.

The uniform ε,γ statement is the correct negation/compactness argument:
its failure supplies one sequence with D≤δ+1/k and every coalition
stage<1/k. The representation is taken from THAT sequence. The positive
stage traced back to it is a contradiction. The number of coalitions
is finite and no uniform bound on t_k is required.

For infinite clocks, censoring moves only finite mass AFTER K_k to Never.
It changes complete debt by an arbitrarily small amount and preserves
every stage event at dates≤K_k EXACTLY; all later stages vanish. It
does not manufacture a cutoff atom. This proves the same universal
statement for arbitrary independent laws and hence arbitrary behavioral
profiles. Every cap in the source, erasure and censoring arguments ranges
over all pure dates and Never; no finite-menu substitution is present.

## Conjecture-facing significance and remaining boundary

The already reviewed implementation comparison distinguishes a terminal-
coalition law atom from an original chronological stage, and a selected
endpoint target from the unchanged near-minimizing whole profile. Those
distinctions remain intact here. The new restriction removes the previous
positive-Never requirement in signed Fin4 and in the nonnegative-own
finite-player case. It consumes the entire fully diffuse actual-minimum
branch, including shared earliest zero-Never endpoints; it does not merely
give another verifier for supplied clocks.

The result still needs a genuine consumer of the forced original
coalition stage. It does not prove that its conditional tail minimizes
debt or that an endpoint purification preserves the whole-profile caps.
The theorem's source and conclusion are nevertheless fully produced
from the actual positive infimum. These open downstream tasks are not
unresolved hypotheses in the stated stage restriction.
