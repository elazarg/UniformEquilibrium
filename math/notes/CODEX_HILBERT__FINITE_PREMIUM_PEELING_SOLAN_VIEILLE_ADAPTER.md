# Finite premium peeling supplies the Solan–Vieille root-choice producer

Author: CODEX_HILBERT.

Status: complete ordinary-mathematical adapter proof, frozen for independent
review. The conditional root-choice mechanism and full-response extraction
are old Solan–Vieille theory. The new input is the explicit finite reward
condition supplied by CODEX_FRECHET_CYCLE. This note does not claim a new
worldwide priority result, a checked Lean adapter, or a solution outside the
stated table class.

## 1. Statement and finite data

Let I be a finite nonempty player set. At the first nonempty quitting
coalition S, player i receives r_i(S); Never pays zero. Strategies are
independent behavioral stopping laws, and every unilateral behavioral
replacement is admissible, including Never and every finite date. Put
s_i=r_i({i}). Assume s_i≥0 and

    r_i(S)≥s_i whenever i∈S.                                  (NN)

Assume also that every nonempty A⊆I has a member i such that

    r_i(S)=s_i for every i∈S⊆A.                               (SP)

Then at every positive error there is an actual terminal approximate Nash
profile. It may be chosen periodic from time zero, and with the same full
terminal error bound in every suffix. Consequently the original table has
one fixed uniform-equilibrium payoff: the target is chosen before the
accuracy, while profiles and horizon thresholds may depend on accuracy.

The claim is for every finite player count. It does not need a punishment
floor, a supplied equilibrium, the polynomial separator, or a positive own
singleton. The compact mesh, period, and positive row-absorption bound may
depend on the table and accuracy; no uniform rate in these parameters is
asserted.

The finite proof that (SP) is equivalent to an ordering in which every
strict own-quitting premium requires an earlier member of its coalition is
in [FRECHET's original](CODEX_FRECHET_CYCLE__FINITE_SUPPORT_QUIT_PREMIUM_PEELING.md),
reviewed at SHA-256
`aff6930efa2be95f654de9097482763fd6103780ff55c09a7059e1491514f329`.

## 2. Unit-singleton root-choice input

First suppose all s_i=1. Let R≥1 bound every absolute terminal reward and
let

    W={v∈[−R,R]^I : v_i≤1 for at least one i}.

For a product root q, write a(q)=1−∏_i(1−q_i) and let F(q,v) be its
expected reward when the all-Continue outcome is paid v. Let Q_i(q) and
C_i(q,v) be its pure Quit and Continue endpoints. Root Nash means each
supported action maximizes those two endpoints.

At every v, finite-game Nash existence supplies an exact root q. If it is
not all-Continue, apply (SP) to A={i:q_i>0}. The selected i has
Q_i(q)=1 because all possible coalitions in its Quit endpoint are contained
in A. Its positive Quit support gives F_i(q,v)=Q_i(q)=1. If q is
all-Continue and v∈W, exact Nash implies v_j≥1 for every j; therefore some
coordinate equals 1 and that player is indifferent between Quit and
Continue.

Thus at every v∈W there is an exact root which is either all-Continue or
has an active quitter receiving at most 1. In fact the latter payoff equals
1. This is precisely the conditional hypothesis of Solan–Vieille (2001),
Proposition 2.2. Their chosen box uses twice the maximal absolute reward;
the same proof works in the reward-containing box W above.

## 3. Charged approximate rows and a finite periodic generator

For completeness, the following is the elementary input and finite-mesh
part of the old argument, with slack constants. It avoids presuming that
the currently hcap-specialized production generator is already generic.

Fix δ∈(0,1]. Choose the exact root and player i from Section 2, and increase
its Quit probability from q_i to q_i+δ(1−q_i). The result q′ has
a(q′)≥δ. If the original i was mixed it was indifferent; if it was surely
Quit it is unchanged; in the all-Continue case the new Quit action is also
indifferent. Its payoff remains exactly 1. Thus F(q′,v)∈W, including the
cube constraint because it is an expectation of rewards and v in the cube.

Every other player's pure-action payoff changes by at most 2Rδ, by
conditioning on i's Bernoulli action. Its support is unchanged. Therefore
each supported action of every player is within 4Rδ of every pure action.
This is SUPPORT regret, not merely ordinary mixed regret.

Given a desired row tolerance τ>0, choose

    δ=min(1/2,τ/(8R)),       ζ=δτ/4.

Take a finite ζ-net of the compact nonempty W with representatives in W.
At each representative choose the preceding row, then map that representative
to a representative within ζ of its successor F. A map of a finite nonempty
set has a directed cycle. Reading that cycle backwards gives a periodic
list of roots q_ℓ and annotations v_ℓ, indexed cyclically, such that

    |v_ℓ−F(q_ℓ,v_(ℓ+1))|∞≤ζ,
    a(q_ℓ)≥δ,
    q_ℓ is support-(4Rδ)-Nash against v_(ℓ+1).

These are independent product rows, not a correlated mixture of roots or
profiles. Repeat the finite list forever. Every suffix terminates almost
surely because survival after n more rows is at most (1−δ)^n. Let U_ℓ
be its ACTUAL terminal suffix payoffs. They obey the exact Bellman identity
U_ℓ=F(q_ℓ,U_(ℓ+1)). Since the prescribed Bellman coefficient is at most
1−δ, maximizing the difference over one period gives

    max_ℓ |U_ℓ−v_ℓ|∞≤ζ/δ.

Each pure endpoint is 1-Lipschitz in its own continuation coordinate.
Consequently all rows are support-(4Rδ+2ζ/δ)-Nash against their actual
next-tail payoffs, with this error at most τ. This proves, from the finite
table itself, periodic support-perfect sequences at every accuracy, with
a common positive absorption bound for the chosen sequence.

This is the finite-mesh construction of Proposition 2.3, with actual-tail
control made explicit. Neither compactness of a selected equilibrium
correspondence nor continuity of a selected root is needed: finite choices
and the finite map suffice. No chronology is required across accuracies.

## 4. Full behavioral extraction: the existing nontrivial consumer

Small support error per row does NOT itself imply small full terminal
regret, even when every suffix terminates. Do not replace this step with
an erroneous direct summation of row errors.

Solan–Vieille Proposition 2.4 (restated as 2.6) is the needed old consumer.
For sufficiently small row error, a sequence whose every suffix terminates
and whose rows are support-perfect against ACTUAL suffix payoffs yields
either the sequence itself as a subgame-perfect approximate equilibrium,
or a stationary approximate equilibrium. Its quoted error modulus is a
sixth root. Only convergence of that modulus to zero is needed here.

The precise production form inspected is
`quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
It requires unit own singletons, not capped joint quitting rewards. For
each desired full terminal error it supplies a positive row tolerance;
periodicity, a positive common absorption bound, and support-perfectness
against actual next-tail values then yield periodic root sequences whose
EVERY suffix is terminal approximate Nash against ALL behavioral deviations.
The stationary alternative is represented as a period-one sequence.

Choose its requested row tolerance before applying Section 3. This closes
the unit-singleton case without any assumptions on passive rewards or
punishment values.

## 5. Zero-singleton closure without changing Never semantics

Now let s_i≥0. For t>0 add t to every nonempty terminal coordinate, leave
Never zero, and divide player i's terminal rewards by d_i=s_i+t>0:

    r̂_i(S)=[r_i(S)+t]/d_i.

The transformed own singleton is 1, and its own premium is
[r_i(S)−s_i]/d_i. Thus both (NN) and (SP) survive exactly. All passive
rewards remain arbitrary finite real numbers. Bounds may grow as t→0;
Sections 2–4 require no bound uniform in t.

For any desired original full terminal error ε>0 choose t=ε/4 and
η=ε/2. Apply the unit result with full error η/max_i d_i. Undoing the
positive coordinate scales gives full error at most η for r+t. For every
actual profile or unilateral replacement π,

    U_i^(r+t)(π)−U_i^r(π)=t·Pr_π(absorption),

so the absolute change is at most t. Hence every original deviation gain
is at most η+2t=ε. This comparison holds separately in every suffix as
well. It covers Never and nontermination; no absorption-one premise is
used for the comparison profile or the deviator.

This is a small-payoff perturbation, NOT an additive affine equivalence
which also shifts the Never outcome. There is no common transformed table
or common period as ε varies. Those are unnecessary for the terminal
all-errors consumer.

Finally apply
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
It selects a single payoff of the ORIGINAL table before accuracy. If all
s_i=0, all-Never is already exact Nash, but this separate shortcut is not
needed for the perturbation argument.

## 6. Exact source and implementation boundary

Primary source checked directly: Eilon Solan and Nicolas Vieille,
“Quitting Games,” Mathematics of Operations Research 26(2), 265–285 (2001),
DOI 10.1287/moor.26.2.265.10549. Original pp.269–272 contain the one-shot
definitions and Propositions 2.2–2.4 with their generation proofs;
pp.272–274 state and explain the nonlocal full-response extraction. The
paper explicitly distinguishes the weaker Proposition 2.2 root-choice
hypothesis from its sufficient capped-reward assumption A.2.
Local inspected copy:
`literature/SOLAN_VIEILLE_2001__QUITTING_GAMES__JSTOR.pdf`.

The corresponding named statements `proposition2_2`, `proposition2_3`,
and `proposition2_4` in `Literature/SolanAndVieille2001.lean` match this
conditional chain. The literature lane is unbuilt and imported nowhere:
these are not cited here as production-checked wrappers.

Production
`exists_quittingPerfectAbsorbingRow_of_soloExitPreference` in
`Classification/Existence/PerfectAbsorbingRow.lean` and
`exists_periodic_quittingPerfectAbsorbingRootSequence_of_soloExitPreference`
in `Classification/Existence/PerfectAbsorbingRootSequence.lean` currently
expose unit-solo AND capped-joint hypotheses. Their finite-mesh mechanism
is the one used above, but a formalizer must expose the weaker root-choice
input or implement this small raw-table adapter. The full-behavior
extraction already has the weaker unit-only signature. A supplied sequence
field would not formalize the producer proved here.

The finite premium-peeling hypothesis itself was not found in the narrow
named source search. Thus the correct description is a new explicit
table-data attachment to an old conditional existence mechanism, not a
new unconditional theorem already named in production, and not merely an
unverified invocation of an old paper claim. The Fin4 polynomial route
remains an independent valid proof for its stated scope; this old-theory
attachment extends the ordinary semantic conclusion to arbitrary finite
player count.

Next requested check: independently verify this complete attachment and
zero-singleton closure before incorporating the all-player conclusion into
a final packet.
