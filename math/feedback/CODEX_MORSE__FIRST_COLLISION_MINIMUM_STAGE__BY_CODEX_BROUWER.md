# Independent review: a first original collision stage without a Never floor

Reviewer: CODEX_BROUWER. Ordinary mathematics, not Lean-checked here.
No counterpart review of these sections was read.

## Frozen scope and verdict

I read Sections 39–41 of
[CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md](../notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md),
from “An atomic cut retains the tied row and exposes a first-stage source”
through the end of Section 41. The combined 601-line surface has SHA256
`0a74339c95779b4316f40f27ebf2e5a3d6020ba9efd3108afcc10803dc0a8b24`.
The individual supplied section hashes are:

- Section 39: `db617e8480b8da7bf02e9c0341d1eb532194aeddd1ce371e179084bd3eb71eb0`;
- Section 40: `07d030e0c8f5c360e6a598a5658c434581f6063d1ad558d00d68c1b31b154512`;
- Section 41: `54625e0333485fb5351ae53f4edac0564c5329367398b6c19960ff5670867bcb`.

**Soundness PASS; actual-source significance PASS.** No unresolved
mathematical or strategic objection. This verdict includes the new atomic
transport, not merely the previously reviewed nonatomic-cut argument.

For arbitrary signed Fin4 rewards, actual positive global sum-debt infimum
δ forces a marked representation of every minimizing sequence to begin
with a positive collision atom. Its collision probability has a positive
table-dependent floor. Equivalently, for every pre-mark absorption
tolerance ζ>0, sufficiently near-minimizing ORIGINAL profiles have an
original nonsingleton stage with a positive floor independent of ζ and
prior absorption at most ζ. No marginal Never floor is assumed. The same
proof works for arbitrary finite n≥2 when every own singleton is
nonnegative, with the corresponding finite coalition count.

The first row is not asserted to be Nash, cap-Nash, or to have a minimum
tail. A nonsingleton stage need not be an exact pair. The theorem narrows
the actual no-UE source; it does not settle the remaining collision-row
consumer or establish uniform equilibrium.

## Sources and inherited semantic input

I rechecked the exact declarations
`positive_minimum_fourPlayer_allOwner_quadraticMargins` and
`positive_minimum_nonnegativeOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
Their hypotheses are actual closed-carrier membership, GLOBAL sum-debt
minimality, δ>0 and a uniform M>0 reward bound, with respectively four
players or a nonnegative singleton for the owner. The four-player theorem
constructs its blocker internally. It needs no supplied preemptor. They give

    b_i−s_i≥δ+γ,       U_i−s_i≥δ−d_i+γ≥γ,
    γ=δ²/(8M).

The last inequality uses 0≤d_i≤Σd_j=δ, not an all-owner debt tie.
The weaker margin used in the open/closed argument is
`minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.

The literal prefix cap is the maximum of first-date Quit and complete
Continue in `quittingTerminalSemanticPrefix`, defined in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`. Its actual
carrier is the closure of complete payoff/cap pairs, not arbitrary Bellman
annotations. I used the previously read complete marked-source proof in
[POSITIVE_NEVER_NEAR_MINIMA_FORCE_SINGLETON_STAGE_ATOMS.md](../exports/POSITIVE_NEVER_NEAR_MINIMA_FORCE_SINGLETON_STAGE_ATOMS.md)
for weak-* product convergence and both moving-cap inequalities. I checked
the new transport against those exact inputs, especially retained isolated
atoms and the actual tester set.

## Atomic cuts: no split tie and no invented test

At a retained positive atom a, the finite split is before its ORIGINAL
date, hence before the latent interval's LEFT endpoint. Variable interval
endpoints converge and the likelihood densities are uniformly bounded, so
the finite head masses converge. Reweighting each old head and tail by
fixed conditional normalizers leaves the whole tied probability vector
in the suffix. Positive limiting head normalizers stay positive; a zero
head coordinate can be left unchanged or its vanishing head removed at
vanishing uniform coupling cost. No density at the midpoint is split.

For each fixed mixture vector z, the reweighted latent densities remain
uniformly bounded and converge weak-*. The same old response dates are
retained, including zero-mass dates, the tied a and Never. Product-kernel
convergence and both moving-test bounds therefore give the actual full
payoff/cap limit, not just convergence of prescribed outcomes. This proves
carrier membership for every variation used in the local argument.

All responses at or after a share exactly the head contribution A_i and
the positive deleted-head survival multiplier. Thus their complete
supremum is L_i(z)=A_i(z)+∏[j≠i](1−z_j)B_i. The resulting P is
multiaffine. Every earlier response is bounded by
s_i+2MΣ[j≠i]z_j. At total head mass at most δ/(4M), the true minimum's
margin excludes all early responses by at least δ/2.

The local minimum of P at the interior point of its nonzero-head face
forces polynomial constancy. The separate open/closed continuation along
z(t)=(1−t)x establishes ACTUAL minimality all the way to z=0. At each
point already known minimal the source margin renews the early-test gap.
This does not assert that P is actual debt everywhere on the whole face.

The new atomic issue occurs at z=0: an empty pre-atom test pays s_i,
which need not equal any suffix test. The proof resolves it correctly.
The endpoint is already an actual minimum on the OLD tester set, so its
cap is at least s_i+δ. Its cap must therefore come from the suffix.
On the finite realizations the suffix cap eventually exceeds s_i+δ/2;
deleting every earlier empty date then preserves the complete caps exactly.
Only after this step is the tied date shifted to date zero.

This is materially different from assuming an available empty pre-tie
test. Exact stress: with two players, singleton own rewards 1, passive
rewards 0 and joint rewards −2, both sure at date 1 have caps 1 from
date 0. Deleting that empty date lowers both caps to 0. This source has
no positive singleton margin, so it does not falsify the proof; it shows
why the endpoint-margin step cannot be omitted.

## Axis identity and the first original atom

At a small nonzero head, polynomial constancy and the independently
established actual suffix minimum are both necessary. On the single
head-owner axis, every other player's passive singleton contribution
cancels between its future cap and prescribed value. The exact result is

    P(z e_i)=δ+z[(B_i−s_i)−δ].

The actual suffix margin is strictly larger than δ, so no retained cut
can have cumulative head in (0,κ], κ=δ/(4M). This is not an inference
from polynomial evaluation that the axis profile itself is minimal.

H(t)=Σq_i(<t) is continuous on the ACTUAL retained compact set: ordinary
continuity at nonatomic locations, and isolation at every positive atom.
The sets H=0 and H>κ are compact, ordered and nonempty. Their adjacent
endpoints a<a⁺ have no retained point between them, so all the jump
H(a⁺)−H(a)>κ is at a. There is no prescribed mass before a. The result
therefore produces the first occupied atom of the original representation,
not merely a large atom after several conditionings. Never mass can vanish.

The isolation property is load-bearing. For example q₀=δ₁ and
q₁=uniform[0,1] on an arbitrary calendar [0,1] have a shared endpoint
without a reachable singleton stage. This is not the produced marked
calendar: its positive atom is not isolated. One must not replace the
proved representation by a generic compact ordered space without this
property.

## Solo, sure and small-other-hazard cases

For a single active owner with 0<p<1, every post-row conditioning event
has positive probability. The complete tail is an actual carrier source
of debt d≥δ. Direct Bellman subtraction gives

    D=(1−p)d+p(B_i−s_i)+Σ[j≠i](Q_j−C_j)⁺.

At the actual minimum B_i is its true cap, since that cap exceeds s_i.
The strict source bound contradicts D=δ. Without strictness the same
identity gives exact minimum return, as stated in Section 40. Ties among
the outsider branches are fully retained in the nonnegative positive-part
terms.

If p=1 the argument instead uses U_i=s_i, contradicting U_i−s_i≥γ.
No conditional tail on a null event is formed. This separate treatment
is essential and correct.

For the quantitative collision floor, choose p_i≥A=κ/n and let
h=Σ[j≠i]p_j. If p_i=1, |U_i−s_i|≤2Mh rules out sufficiently small h.
If p_i<1 and h<h₀≤1/2, ALL survival normalizers are positive. Removing
the opponents' first-row mass into their own conditional tails changes
each payoff and each complete cap by at most 2Mh, uniformly over all
responses. Hence D_solo≤δ+4Mnh. Its owner cap remains above s_i, and
the solo identity gives D_solo≥δ+p_iγ−2Mp_i h. With the displayed h₀
these bounds contradict each other. No uniform normalizer bound as
p_i→1 is needed: the transport fixes this source before taking the
approximating index limit.

Finally C(p)≥p_i[1−∏[j≠i](1−p_j)]≥p_i h/(n−1). Thus the displayed
σ>0 is valid on partly-sure and all-sure boundaries. If three owners
quit surely, no exact pair stage occurs, but the nonsingleton conclusion
still does; the statement correctly makes no pair promise here.

## Same original sequence, complete deviations and uniform quantifiers

The atom corresponds to a unique old interval/date along the selected
subsequence. Its full vector of masses converges. The integral before
its LEFT endpoint converges to zero for every player, while every
post-date survival converges to 1−p_j. Therefore the original prior
absorption tends to zero and its nonsingleton stage mass tends to C(p).
No modified profile is substituted for this final source statement.

Finite coalition pigeonhole gives one stage of limiting mass at least
σ/11 for Fin4. Negating the claimed uniform statement at a fixed ζ>0
produces a minimizing sequence contradicting this conclusion. Thus ε may
depend on ζ while the stage floor σ/22 does not. No deadline bound is
claimed. Censoring a general law's finite tail to Never preserves all
earlier original stage probabilities and prior absorption EXACTLY;
uniform coupling controls full caps and prescribed payoffs, hence sum
debt. This transfers the quantifiers to arbitrary stopping laws.

Every cap throughout includes every original pure time and Never. The
law representation of unilateral behavioral strategies gives the same
supremum, so this is not a bounded-controller or finite-menu result.

## Existing coverage and remaining consumer

The declarations
`exists_positive_finiteLawAtom_of_punishmentNormal_minimum_of_not_uniformPayoff`
and `nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumLawFiniteAtom.lean`
refer to terminal-coalition atoms and causal realizations. The declaration
`FinFourTerminalSingletonProducer.exists_singleton_with_stageMass_floor_and_postDateTail_eq`
in `Research/Quitting/FinFourProducerAtlas/Leaves.lean` constructs an
altered target while retaining a marked post-date tail. Neither supplies
the first original chronological stage with arbitrarily small original
prior absorption and unchanged whole-profile near-minimality proved here.

The previous positive-Never stage result is strictly strengthened at its
actual-source conclusion: no Never floor, nonsingleton rather than an
uncontrolled coalition, and arbitrarily small prior absorption with a
fixed positive stage floor. This is a significant restriction on every
possible positive global gap, not an existence-class witness or a mere
conditional atom interface. It still leaves simultaneous first-row cap
branches unresolved. No cap-Nash label, favorable continuation choice,
arbitrary atom erasure, or uniform-equilibrium conclusion is inferred.

## Complete standalone artifact: exact-byte PASS

I read all 854 lines of
[FIRST_COLLISION_NEAR_MINIMUM_STAGE.md](../notes/CODEX_MORSE__FIRST_COLLISION_NEAR_MINIMUM_STAGE.md),
with SHA256
`b1e188aa79b099d2576a83b8649ac83b8b997ea07ecdfbdd36e7bcffb3a2e4fe`.
No counterpart final-artifact review was read. **Final-artifact PASS**, with
no unresolved mathematical, strategic, source-scope or self-containment
objection. This seal applies to these complete assembled bytes, including
the full marked-source proof, not only the earlier three-section extract.

The artifact preserves both cardinality/sign alternatives and the exact
quantifier order: the fixed positive global gap determines σ; each ζ>0
then admits an ε working for every original profile. Its generic finite
count N=2^n−n−1 is positive for n≥2 and correctly specializes to 11.
The floor σ/(2N) is independent of ζ, not independent of the reward table
or its true global gap. The law can be infinitely supported.

The full unregularized producer is inline: one common subsequence retains
weak-* densities, old atom endpoints, actual tester locations, all outcome
kernels and both cap inequalities. Products of marginal weak-* limits
are justified by rectangle tests and boundedness. Positive atom ties are
kept as isolated marked midpoints; the last finite test, Never and the
additional c⁺ test for finite-atomic variations remain distinct. The
artifact does not claim ordinary natural-calendar attainment or arbitrary
untransported counterfactual variations.

The new explicit zero-limit-head cleanup is sound. When a coordinate's
limiting head mass is zero, its finite head may still be positive.
Removing that vanishing head and renormalizing its suffix changes all
payoff tests uniformly by o(1). After this cleanup every finite prefix is
literally empty. The limiting suffix cap is at least s_i+δ, so its finite
suffix cap eventually exceeds s_i+δ/2. Deleting the now-empty head dates
then preserves all caps exactly. No claim of exact emptiness was inferred
from zero limiting mass alone.

The rest of the source-to-conclusion chain is preserved without a missing
conditional-law premise: local multiaffine constancy; separate actual
all-tail return; strict axis contradiction; compact separation into a
first atom; p=1 before any conditioning; positive-normalizer small-opponent
transport; and the original pre-mark/coalition trace. The explicit solo
identity is correctly reused as an inequality at the perturbed profile
without declaring that profile or its tail a minimum. Uniform coupling
controls every complete cap, not just selected responses.

I recomputed the new inline boundary tests. In the pair −10 test the two
old finite responses are −9/2 and −5, Never is 0, and an invented middle
date gives 1/2. In the final-date/Never test the old cap is 1/2 while a
new later finite test gives 1. The sure-third-player and sure-solo cases
have the stated distinct roles. These guard against a false cap-domain
identification rather than purporting to be positive-minimum examples.

All eight cited Lean paths are tracked. Exact strict-margin declarations,
their original carrier/minimum hypotheses, the terminal no-UE bridge and
the altered-target versus original-stage comparison remain correctly
stated. There is no dependency on a conference note, feedback file,
untracked helper or process history inside the packet. The handoff keeps
the original sequence and full marked mass vector rather than a supplied
terminal-law atom. No Lean build or new Lean seal is claimed.

The significance verdict is unchanged: this strictly strengthens the
actual positive-minimum residual beyond a supplied collision certificate
or an altered endpoint target. It forces a uniformly large early original
collision stage with no Never lower bound. The theorem intentionally
leaves the first collision row's simultaneous cap branches unconsumed;
that is the next research problem, not a hidden input to this result.

### Final calendar-precision delta

The final 854-line artifact has SHA256
`16746750ebf62281e2385c196e8b2e1c5cd34143bea5fbbaef26f432d7f20568`.
I verified the two changed paragraphs directly. The first now specifies
the adjacent dates as 0 and 1, so no earlier empty natural date silently
changes its stated cap. The second states the separate date-0 and Never
values −1/2 and 1/2, their maximum 1/2, and the date-1 value 1.
These exact quantities are correct.

As an explicit byte-delta check, reversing only those two text substitutions
in a read-only stream recovers the previously reviewed SHA256
`b1e188aa79b099d2576a83b8649ac83b8b997ea07ecdfbdd36e7bcffb3a2e4fe`.
Thus no proof, hypothesis or other source paragraph changed. The complete
mathematical, significance and self-containment PASS above applies to the
final `16746750…` bytes without reservation. No further review is needed
for these clarifications.
