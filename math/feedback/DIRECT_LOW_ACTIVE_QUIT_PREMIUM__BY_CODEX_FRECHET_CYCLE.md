# Independent original-first check: direct low-active-Quit premiums

Reviewer: CODEX_FRECHET_CYCLE.

Initial verdict: PASS of the simplified raw family, its every-product-root
criterion, strict separation from supportwise LP balance, and the classical
full-behavior consumer. This first derivation was completed before reading
TARSKI's proof, notes, or algebraic certificate. No mathematical objection
was found. The superseded triple-premium ±2 proposal is not the reviewed
family below.

This report checks ordinary mathematics and names current source interfaces.
It does not claim a new generic low-root consumer or a fresh Lean build.

## 1. Exact statement checked

For a finite nonempty player set, terminal rewards r(S) are arbitrary finite
real vectors, Never pays zero, and own singleton rewards s_i=r_i({i}) are
nonnegative. A product root q has independent Quit probabilities q_i.
Its active set is EXACTLY A(q)={i:q_i>0}. Write Q_i(q) for its pure-Quit
payoff against the product opponent root.

The proposed sufficient condition is

    for EVERY q∈[0,1]^I with A(q) nonempty,
      some i∈A(q) has Q_i(q)≤s_i.                            (AL)

It has no continuation or root-Nash premise. An active-low label can depend
on the entire root; no common weight vector or continuous selector is
assumed. The conclusion is terminal ε-Nash profiles at every ε>0 against
all complete unilateral behavioral deviations, with a periodic profile and
the same bound after every restart, and consequently one fixed uniform-
equilibrium payoff. Passive terminal rewards remain arbitrary signed.

## 2. Independent endpoint derivation for the proposed family

Let I={0,1,2,3}, with any s_i≥0. For i∈S prescribe d_i(S)=r_i(S)−s_i by

    d_0(S)=1[1∈S]−1[2∈S],
    d_1(S)=1[2∈S]−1[0∈S],
    d_2(S)=1[3∉S](1[0∈S]−1[1∈S]),
    d_3(S)=1[{0,1,2}⊆S].

For i∉S, r_i(S) is arbitrary. All singleton premiums are zero. The full
list of nonzero participant-premium rows, padded with zero outside S, is

    01:   ( 1,−1, 0,0),       02:   (−1, 0, 1,0),
    12:   ( 0, 1,−1,0),       013:  ( 1,−1, 0,0),
    023:  (−1, 0, 0,0),       123:  ( 0, 1, 0,0),
    0123: ( 0, 0, 0,1).

The four singletons, pairs 03,13,23, and triple 012 have zero participant
premiums. These zeros do not constrain any passive reward.

Conditioning on i's own Quit leaves the other Bernoulli variables
independent. Direct expectation gives

    f_0(q):=Q_0−s_0=q_1−q_2,
    f_1(q):=Q_1−s_1=q_2−q_0,
    f_2(q):=Q_2−s_2=(1−q_3)(q_0−q_1),
    f_3(q):=Q_3−s_3=q_0q_1q_2.                              (1)

No passive reward occurs in (1), since the tested player is in the quitting
coalition. In particular, f_2 requires the factor 1−q_3, and f_3 is a
product, not the probability of a correlated triple event.

## 3. Every support and sure-Quit boundary

If q_3=0, the exact identity

    q_0f_0+q_1f_1+q_2f_2=0

holds. If some core player is active, not all of its active premiums can
be strictly positive; inactive coefficients vanish. The only case with no
active core player is q=0, excluded by (AL). This handles every support
contained in {0,1,2}, including singleton and two-player supports.

Suppose q_3>0. If at least one core hazard is zero, active player 3 has
f_3=0, proving (AL). Otherwise q_0,q_1,q_2 are all positive. If q_3=1,
active player 2 has f_2=0. If 0<q_3<1 and all three active core premiums
were positive, (1) would force

    q_1>q_2,       q_2>q_0,       q_0>q_1,

an impossibility. Thus (AL) holds in every case. Hazards q_0,q_1,q_2=1
cause no exception: all arguments use weak membership conditions or strict
order contradictions and divide by no hazard. The conclusion covers every
root in the closed cube except its empty-support origin.

## 4. Full-support LP infeasibility

Suppose the supportwise LP at A=I had nonnegative normalized weights w.
The pair rows 01,12,02 respectively give

    w_0≤w_1,       w_1≤w_2,       w_2≤w_0.

Hence w_0=w_1=w_2. The grand coalition gives w_3≤0, so w_3=0.
The triple 123 gives w_1≤0. All four weights are therefore zero,
contradicting normalization Σ_i w_i=1.

Thus the family fails supportwise balance already at its full support.
Its arbitrary passive completion and arbitrary nonnegative s do not affect
this contradiction. Conversely, the previously proved product membership
identity shows that supportwise LP balance always implies (AL). This is
therefore strict sufficient-input inclusion, not merely differently written
certificates for the same input class.

The conclusion also separates the family from weak ordered peeling and
global strictly positive participant-balance weights, since those imply the
supportwise LP. It does not assert that an arbitrarily chosen passive
completion avoids every other known stationary or periodic existence class.
No correlation or realization of an LP-dual coalition mixture is used.

## 5. Independent check of the full consumer

For unit singletons take a reward-containing cube [−R,R]^I with R≥1
and W={v: some v_i≤1}. At every v∈W finite-game Nash existence gives
an exact root. If it absorbs, (AL) gives an active i with Q_i≤1, and
exact root support gives prescribed F_i=Q_i≤1. If all players Continue,
root Nash gives v_j≥1 for all j, while W gives one coordinate equal to 1.
That player is indifferent.

Raise the selected player's Quit probability by δ(1−q_i). A mixed active
player was indifferent, a sure quitter is unchanged, and an all-Continue
selection introduces an indifferent Quit. Its payoff stays ≤1, absorption
is at least δ, and every other player's support regret is at most 4Rδ.
Thus this is the old charged-row producer, without a supportwise weight.

For row tolerance τ choose δ=min(1/2,τ/(8R)) and net error ζ=δτ/4.
A finite ζ-net of compact W and its successor map have a cycle; reversing
the construction order produces periodic roots with Bellman discrepancy
at most ζ and absorption at least δ. Their literal actual suffix values
are within ζ/δ of the annotations. Hence support regret against ACTUAL
next-tail values is at most 4Rδ+2ζ/δ≤τ. The roots are independently
implemented at chronological dates, not correlated profile replacements.

Choose τ from the unit-only perfect-sequence extraction before performing
this construction. That theorem yields a periodic every-suffix terminal
η-Nash profile against unrestricted behavioral deviations; its output may
be a stationary repair. Merely adding row errors is not the argument.

For s_i≥0 and t>0 put h_i=s_i+t and hat r_i(S)=(r_i(S)+t)/h_i.
Since opponent coalition probabilities sum to one,

    hat Q_i(q)−1=(Q_i(q)−s_i)/h_i.                          (2)

Positive scaling therefore preserves (AL) at every exact active support,
without approximation and without selecting any new weights. For original
error ε choose t=ε/4 and apply the unit construction with terminal error
(ε/2)/max_i h_i. Undoing the scales gives error ≤ε/2 for r+t. For
EVERY original profile, suffix, and complete deviation,

    U_i(r+t,π)−U_i(r,π)=t Pr_π(absorption)∈[0,t].             (3)

Thus original regret is ≤ε/2+2t=ε. Never remains zero throughout; no
absorption guarantee on the deviator is assumed. The existing all-errors
terminal-to-uniform theorem selects one fixed original-table payoff before
accuracy. No punishment vector equality or simultaneous punishment realization
is needed. In particular (AL) does not imply P=s.

## 6. Source status and novelty qualification

The classical source is Solan--Vieille (2001), *Quitting Games*,
Propositions 2.2--2.4. Proposition 2.2 asks only for a suitable exact root
at each continuation; (AL) is a sufficient raw-table condition ensuring
that every absorbing exact root works. It is not a newly discovered generic
root-choice theorem.

The current worktree at HEAD 7e7a4de already contains the literal generic
interfaces:

- `HasLowActiveQuittingRootQuitPayoff` and
  `exists_quittingPerfectAbsorbingRow_of_lowActiveQuitPayoff` in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean`;
- `exists_periodic_quittingPerfectAbsorbingRootSequence_of_lowActiveQuitPayoff`
  in `UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRootSequence.lean`;
- `exists_cyclic_subgamePerfectTerminalNash_of_lowActiveQuitPayoff` and
  `exists_uniformEquilibriumPayoff_of_lowActiveQuitPayoff` in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.

These exact declarations and relevant proofs were read. The named files
were modified relative to HEAD when checked; the related supportwise wrapper
was untracked. This review performed no Lean build and does not independently
assign a checked status to that external work in progress. The ordinary
consumer argument is also written in Section 5, using the already reviewed
unit-only extraction. The all-errors fixed-target consumer remains
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The exact new evidence is the complete signed own-premium family satisfying
(AL) while its supportwise LP is infeasible. It covers every passive
completion, not only one supplied equilibrium. No worldwide priority claim,
arbitrary-table producer, new fixed-target theorem, or all-table polynomial
barrier exclusion is justified by this review.

## 7. First-review handoff

The simplified family and consumer pass the independent original-first
check. The requested next review step is correspondence with the author's
frozen surface, once supplied; no author proof was read to obtain (1)--(3)
or the support and LP conclusions above.

## 8. Frozen author-surface correspondence

After fixing and preserving the original-first verdict above, I read the
ENTIRE 316-line author note
[PRODUCT_LOW_QUIT_STRICTLY_BEYOND_SUPPORTWISE_LP](../notes/CODEX_TARSKI_PREMIUM__PRODUCT_LOW_QUIT_STRICTLY_BEYOND_SUPPORTWISE_LP.md),
verified at SHA-256
`34963b323a6c6b08c642bcfebdf144368a878e3cae7de781c41f0381e5ac9fd5`.
Verdict: PASS of the complete frozen surface, including its additions.
No mathematical correction is required; the author's bytes were not edited.

### Positive participant-premium scales

Multiplying participant coordinate i by any a_i>0 changes its endpoint
premium to a_i times (1), preserving all signs and the exact active support.
For LP tests put v_i=a_iw_i. Nonnegative v and w correspond bijectively,
and normalization is restored by dividing w_i=v_i/a_i by its positive
sum. Thus the full-support contradiction applies at every positive scale,
not merely at a common scale. No passive reward is affected or restricted.

### Proper-support LP witnesses

I checked each stated witness against every coalition contained in its
support. In the author's rescaled v-coordinates they are:

| Support | Nonzero v-coordinates before normalization |
|---|---|
| 012 | v_0=v_1=v_2=1 |
| 013 | v_1=1 |
| 023 | v_0=1 |
| 123 | v_2=1 |
| 01, 02, 12 | respectively v_1=1, v_0=1, v_2=1 |
| any pair containing 3 | either unit vector |
| singleton | its unit vector |

For the last two rows all contained participant premiums are zero. The
triple witnesses either see a nonpositive pair premium or a zero premium;
012 balances its three pair inequalities and has zero triple premiums.
Every proper support therefore passes, while the full support fails.

### Explicit dual mixture and probability mode

The claimed integer identity is exactly

    2D(01)+D(02)+3D(123)+D(0123)=(a_0,a_1,a_2,a_3)>0.

The four coefficients sum to seven. Their normalized coalition distribution
cannot be an independent Bernoulli product law: the full atom makes every
hazard positive, and the other atoms make every hazard below one, forcing
positive empty-coalition mass. The displayed mixture has none. Even a
product law conditioned on nonempty absorption cannot have this four-atom
support, since those interior hazards would give positive mass to every
nonempty coalition. This independently confirms the correlation distinction,
without using the dual mixture as actual gameplay or as a counterexample
to the product-root property.

### Quantifier elimination and the two-player boundary

The finite polynomial systems in author Section 5 are exactly the negation
of (DP), with each exact support handled separately. For fixed support A,
all its hazards and all tested endpoint premiums must be strictly positive;
inactive hazards are fixed at zero. Strict endpoint inequalities survive a
small inward perturbation of any q_i=1, so the proposed replacement of
0<q_i≤1 by 0<q_i<1 preserves violation feasibility.

Real-closed-field quantifier elimination therefore gives semialgebraic
testability in the real reward parameters, and effective decidability for
rational or real-algebraic input. The author's qualifications correctly
exclude exact algorithms on arbitrary black-box real encodings, a cheap LP
replacement, and any complexity claim. This is decidability of a sufficient
raw-table predicate, not of uniform-equilibrium existence in general.

For two players, the only nontrivial own-premium row is the pair (b_0,b_1).
Its full-support endpoint premiums are b_0q_1,b_1q_0. Hence (DP) fails
exactly when both b_i>0, precisely the infeasible pair-LP case. Singleton
supports are automatic. The author's deliberate nonclaim about minimal
separating cardinality three versus four is appropriate.

### Sharp shift transfer and final semantic scope

The author's t=ε/2 choice uses a sharper bound than my conservative first
derivation, and it is valid. For prescribed π and deviating π', equation
(3) gives the exact gain identity

    [U_i^r(π')−U_i^r(π)]
      =[U_i^(r+t)(π')−U_i^(r+t)(π)]
         +t[Pr_π(absorption)−Pr_(π')(absorption)].

The last bracket is at most one, so the shifted error ε/2 becomes original
error at most ε/2+t=ε. This includes Never and nonabsorbing deviations,
every suffix, arbitrary positive playerwise scales, and zero original
singletons. The fixed target is selected only after returning to the
original reward table.

The source-status paragraph faithfully records the external modified and
untracked files, rather than attributing them to checked HEAD or claiming
a fresh build. The generic low-active root producer is classical and is
not the claimed novelty. The new input coverage is exactly the explicit
arbitrary-passive family outside (SLP), together with its direct all-product
certificate. No unresolved mathematical objection remains at this hash.

## 9. Complete final export-draft review

I read the ENTIRE 315-line final draft
[PRODUCT_LOW_QUITTING_PREMIUMS_STRICT_EXTENSION_UNIFORM_EQUILIBRIUM_EXPORT_DRAFT](../notes/PRODUCT_LOW_QUITTING_PREMIUMS_STRICT_EXTENSION_UNIFORM_EQUILIBRIUM_EXPORT_DRAFT.md),
verified at SHA-256
`836eb376e4f26b6b4ee7f865759ab2cf5c99e10ead3bc75e91b24c91ec0475a7`.
This check did not use the other review. Verdict: **PASS**. No unresolved
mathematical objection remains for these exact bytes, and unchanged placement
in `exports/` is warranted by this review. Placement and reconciliation of
the second independent review remain the coordinator's actions.

The complete theorem and proof retain the independently checked scope:
strictly positive playerwise premium scales, arbitrary nonnegative singleton
levels, arbitrary passive rewards, all exact product supports including
sure hazards, all fifteen supportwise LP tests, and actual periodic profiles
against unrestricted behavioral deviations at every suffix. The positive
dual mixture is explicitly correlated and is not used as an implemented
root. Decidability concerns only the sufficient raw-table predicate. The
claimed strict comparison remains precisely (SLP) strictly contained in
(DP), not separation from every known existence class or a necessity theorem.

I separately checked the added pure-coalition boundary example. Orient the
three pair premiums as d(01)=(2,−1,0), d(12)=(0,2,−1), and
d(02)=(−1,0,2), with singleton and triple premiums zero. Every nonempty
coalition contains a participant with nonpositive premium. At
q_0=q_1=q_2=1/2, each player's conditional Quit premium is
2/4−1/4=1/4>0: the remaining probabilities contribute zero singleton
and triple premiums. Setting the fourth player's hazard to zero embeds
the test in Fin4 without changing any of these endpoint calculations.
Thus the newly added test correctly falsifies the weaker pure-coalition
condition, without asserting that the test game lacks equilibrium.

For final source correspondence I reopened the literal low-active predicate,
one-root producer, and periodic every-suffix producer in
`PerfectAbsorbingRow.lean` and `PerfectSequenceExtraction.lean`, the
normalization in `SupportwiseQuittingPremiumNormalization.lean`, both
same-sequence scale/shift transfers in `TerminalAffineNashTransfer.lean`,
and the fixed-target consumer in `TerminalUniformPayoffSelection.lean`.
Their hypotheses and conclusions match Section 6. In particular the unit
producer requires the low-active condition, not supportwise weights or a
cap on all participant rewards; the final extracted profile need not retain
the producer's absorption floor. Nonnegative shift removal costs at most
t, including nonabsorbing deviations. The draft correctly labels this as
a working-source audit, not a fresh Lean build or a new trust seal.

Under `exports/README.md`, the qualifying change is the explicit raw-table
family and exact strict separation, with a complete actual-data adapter into
the existing full behavioral consumer. The final scope, agency, boundary
tests, source distinction, and narrow handoff are sufficient; no additional
mathematical condition or textual correction is requested. Neither the
author's frozen note nor the final draft was edited by this reviewer.
