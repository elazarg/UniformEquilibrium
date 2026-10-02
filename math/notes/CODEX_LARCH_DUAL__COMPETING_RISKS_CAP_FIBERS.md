# Competing-risks identification and finite dated-law cap fibers

Author: CODEX_LARCH_DUAL.

Status: ordinary mathematical proof sketch, independently reviewed by
[CODEX_LARCH_GEOMETRY](../feedback/CODEX_LARCH_DUAL__COMPETING_RISKS_CAP_FIBERS__BY_CODEX_LARCH_GEOMETRY.md)
with no unresolved mathematical objection; not Lean-checked or exported.
This is an outside-field visit to survival analysis
and partial identification, connected to `NL-06` and `NL-08` in the
[nonlocality catalogue](../ideas/NONLOCALITY_TECHNIQUE_CATALOGUE.md).

**Current conclusion:** a finite dated terminal law admits an explicit
product-compatibility test. Among its actual independent-profile realizations,
all response caps are identified except possibly ONE coordinate. That
coordinate's closure is an explicit interval, and its lower endpoint is
implemented approximately by an existing stationary punishment theorem.
This is a candidate unifying identification result, not a new punishment
producer or an unrestricted compactification theorem.

## 1. Outside-field question and its limits

In competing-risks survival data one observes the first event time and its
cause, while later latent event times are censored. Here the observable is
the first quitting date together with its entire tied coalition. Independent
private stopping clocks are the model assumption, and deleting one player's
clock is the intervention relevant to that player's complete response cap.

[Tsiatis, “A nonidentifiability aspect of the problem of competing risks,”
1975](https://pmc.ncbi.nlm.nih.gov/articles/PMC432231/) shows in its Theorem 2
that crude cause-specific survival observations do not identify marginal
latent survival laws without an independence assumption. That paper motivates
the identification question; its theorem is not invoked here. Our assumptions
are stronger in two explicit ways: independent latent clocks are part of the
quitting-game semantics, and simultaneous causes are observed as a full
coalition. All formulas below are proved directly for discrete time.

The existing [continuation-state investigation](../ideas/CONTINUATION_GAME_STATE/README.md)
already records the full response graph, its exact prefix action, failures of
horizontal replacement, and arbitrary compact infinity fibers. Reintroducing
that whole state would add nothing. The narrower question is:

> Given only one finite DATED terminal probability law, which full behavioral
> response caps are identified across all actual independent realizations,
> and which can be improved without changing that law?

This retains the order of the observed events. It does not claim that an
unmarked coalition law has the same information.

## 2. Data and finite product-compatibility theorem

Let I have n≥2 players, with rewards r_i(S) for nonempty coalitions S and zero
at Never. All unilateral deviations are arbitrary complete stopping laws on
the nonnegative integers plus Never; no public correlation is introduced.

Supply nonnegative masses μ(t,S), 0≤t<N, for nonempty S⊆I and μ∞≥0,
with total sum one. There is no finite terminal mass after N−1. Define

    R_t = μ∞ + Σ_(u≥t,S) μ(u,S),        0≤t≤N,
    m_i,t = Σ_(S containing i) μ(t,S).

R_t is probability of reaching date t. At every date with R_t>0, define

    q_i,t = m_i,t/R_t.                                      (1)

**Finite compatibility theorem draft.** The supplied μ is the dated terminal
law of actual independent stopping clocks if and only if, at each positive-
reach date and every nonempty S,

    μ(t,S)/R_t = ∏_(i∈S) q_i,t ∏_(i∉S) (1−q_i,t).          (2)

Necessity: conditioned on every clock surviving before t, independence
persists. Summing the root coalition probabilities over coalitions containing
i gives that player's conditional probability of stopping at t, proving
(1). The product-root law gives (2).

Sufficiency: use the q_i,t as independent behavioral hazards while R_t>0,
and choose all-Continue otherwise. Summing (2) over nonempty S shows that
the product Continue probability is R_(t+1)/R_t. Thus the reconstructed
reach probabilities telescope to R_t and reproduce every μ(t,S) and μ∞.
After N use all-Continue. This constructs actual independent clocks.

This is finite algebra. After clearing denominators, (2) becomes

    μ(t,S) R_t^(n−1)
       = ∏_(i∈S) m_i,t ∏_(i∉S) (R_t−m_i,t).                (3)

At R_t=0, all displayed row masses already vanish by nonnegativity, and (3)
is automatically satisfied. Hence (3), nonnegativity, and normalization
give a finite polynomial description, without separate unidentified root
variables. This does not remove the need to record the calendar.

## 3. The first loss of identification is a sure-absorption row

Suppose μ passes the test. All actual profiles realizing μ must have the
same conditional hazards q_i,t at every R_t>0. There are two cases.

If μ∞>0, every R_t>0. After the last observed finite date, each conditional
hazard is zero, since any positive one would produce additional finite mass.
Thus every complete stopping law is determined, and so is every response cap.

If μ∞=0, let H be the last date with positive reach; then R_H>0 and
R_(H+1)=0. From the product Continue probability, at least one player has
q_i,H=1. Let K={i:q_i,H=1}. The prescribed hazards through H are identified;
the opponent prescriptions after H are invisible on the equilibrium path.

If |K|≥2, deleting any one player leaves a sure quitter at H. Hence no
unilateral response ever sees the hidden suffix. Every pure response at or
before H has an identified value, and all finite responses after H are
equivalent to Never. Consequently ALL full caps are identified.

If K={o}, deleting any j≠o leaves o surely stopped by H. Thus every B_j,
j≠o, is still identified. Only deleting o can expose the hidden suffix.
That single exception is the entire cap ambiguity of an exact finite dated
outcome law. It is not an arbitrary family of independent cap defects.

The hidden suffix may still have infinitely complicated response graphs.
The claim concerns one scalar full cap, not graph reconstruction or renewable
horizontal replacement.

## 4. Exact one-coordinate cap fiber

Assume K={o}. The observed prefix determines the joint law of the opponents'
stopping times through H. Write

    ρ = Pr(all opponents of o stop strictly after H)>0,
    A = E[r_o(S_opponents); first opponent event occurs by H],
    C = max_(0≤t≤H) V_o(t).

The expectations in A ignore o completely. These quantities are computed
from the identified hazards by the ordinary product formula; they are not
obtained by conditioning the observed terminal law after absorption.

Conditional on all opponents surviving beyond H, their future clocks remain
independent. Their laws may be chosen arbitrarily without changing μ. If b
is o's full response cap against that conditional opponent suffix, then

    B_o = max{C, A+ρb}.                                  (4)

Indeed the prefix tests are exactly those in C. Every later or Never response
receives the fixed early contribution A, plus ρ times its suffix response
payoff. Taking the supremum gives (4), without response attainment.

Let

    v_o = inf_(independent opponent suffix laws) b,
    R_o^+ = max({0} ∪ {r_o(S):S nonempty}).

The quantity v_o is precisely the existing quitting punishment value, not a
new open infimum introduced by this note. The exact behavioral/stationary
identity is already supplied by `quittingPunishmentValue_eq_stationaryPunishmentValue`
(`UniformEquilibrium/Quitting/Stationary/MinMax.lean`).

**Cap-fiber closure theorem draft.** Across all actual independent profiles
with dated law μ, the closure of the possible cap vectors is a line segment.
Every nonowner cap is fixed, and the owner coordinate ranges over

    [ max{C,A+ρv_o},  max{C,A+ρR_o^+} ].                  (5)

Proof sketch: b is at least v_o and at most R_o^+. The upper endpoint R_o^+
is attained by a deterministic opponent coalition at the first suffix date
and an appropriate responder choice, or by all-Never if the maximum is zero.
For a singleton {o} maximizer, all opponents Never and immediate o-Quit
attains it. For every other maximizing coalition, choose its opponent members
to stop together at that first suffix date, and let o either join or Never
as appropriate. No cap can exceed the largest reward.

The set of opponent stopping-law tuples is path connected under coordinatewise
convex interpolation. Full cap is continuous along such paths: product-law
total variation controls every response payoff uniformly by a finite reward
bound, and therefore controls their supremum. Its image is consequently an
interval. Its infimum is v_o and its attained supremum is R_o^+, so its
closure is [v_o,R_o^+]. Formula (4) proves (5). The lower endpoint need not
be attained by an actual profile; closure is intentional.

The stationary punishment approximation realizes the lower endpoint with
arbitrarily small error and EXACTLY the same dated law μ. All other cap
coordinates and every prescribed payoff remain exactly fixed. Quantitatively,
an ε-accurate suffix punishment incurs owner-cap error at most ρε.

## 5. Concrete payoff/incentive consumer

The outside-field reconstruction supplies a finite-data version of the
following safe repair:

    realizable finite dated law μ
      → identified prefix hazards
      → no cap ambiguity, OR one unique-sure owner o
      → stationary completion minimizing that owner's cap in its law fiber.

Unlike a generic best-response or coordinate repair, this completion changes
no prescribed payoff and increases no other player's cap. It therefore
minimizes BOTH maximum debt E and total debt D within the same dated-law
fiber, up to arbitrary positive error. A sufficient equilibrium certificate
can be checked directly: all identified nonowner debts are small, and

    max{C,A+ρv_o} − U_o(μ)

is small. This gives a canonical completion to a supplied finite outcome-law
candidate while retaining full behavioral deviations.

The consumer does not generate μ from arbitrary rewards. Exact unmarked
payoff/calendar compression may change dated μ or lose its product tests.
This note therefore does not bridge that existing compression automatically.

The existing instant-punishment theorem is the H=0, pure singleton instance.
The existing sure-base cap rigidity handles the |K|≥2 phenomenon even on a
larger undated semantic-law carrier under its additional hypotheses. What
this candidate might add is one identification theorem organizing arbitrary
finite dated laws, with a sharp one-coordinate fiber and an algorithmic
product-compatibility test. Its strategic ingredient is already present.

## 6. Exact tests and falsifiers

Two players already give a nontrivial interval. Let player 0 quit surely at
date zero, set r_0({1})=1 and every other reward coordinate to zero. Compare
opponent 1 playing Never with opponent 1 quitting at date one. Both profiles
have exactly the same dated law, concentrated on {0} at date zero. Their
player-0 caps are respectively zero and one. Mixing these two opponent laws
fills the entire interval [0,1]. Here C=A=v_0=0 and ρ=R_0^+=1.

Two sure quitters are the contrasting positive test: if both players quit
surely at zero, deleting either leaves the other surely quitting, so all
response caps are determined by the root table and hidden prescriptions are
irrelevant.

The exact compatibility check must reject any alleged single root whose
coalition masses fail product factorization. For example a one-date law with
mass 1/2 on singleton {1} and 1/2 on singleton {2}, and no Never mass, has
q_1=q_2=1/2 but assigns zero to the pair and to Continue, contradicting (2).
The same UNMARKED coalition law can be realized by a chronology, which shows
why the date is indispensable.

Do not extend (5) to arbitrary jointly compactified response graphs: the
[infinity-fiber universality example](../ideas/CONTINUATION_GAME_STATE/INFINITY_FIBER_UNIVERSALITY.md)
rules out a finite graph description. Do not claim horizontal closure:
[the replacement no-go](../ideas/CONTINUATION_GAME_STATE/HORIZONTAL_REPLACEMENT_NO_GO.md)
already shows that even complete unary response graphs fail it. The proposed
completion has a special causal shield: a sure player ends the prescribed
path, so only its own deletion reaches the modified suffix.

## 7. Priority and next question

This is a moderate-value mathematical unification candidate with a small
implementation footprint if its exact identification statement is absent.
It is a low-confidence new UE attack: its off-path optimization is already
the punishment theorem. The useful next test is whether an existing
payoff-fiber producer outputs a finite DATED law satisfying (3), and whether
the canonical completion improves its cap estimate compared with the current
consumer. If no such producer exists, retain the identification theorem as a
compression/audit tool rather than enlarging it into a universal state theory.

The genuinely harder continuation is quantitative: near a sure-absorption
row, can the exact one-coordinate ambiguity be replaced by a controlled
small set of deleted-tail errors, with constants governed by opponent reach
rather than inverse individual Never mass? That is not proved here. Existing
near-sure-root coupling must be checked before treating it as a new lemma.

## 8. Source and overlap audit

Read the catalogue and the continuation-state README, next questions,
replacement no-go, Never-mass fiber bound, and infinity-fiber universality.
These prevent advertising the present finite identification as a general
compactification or a new full response graph.

Lean sources inspected statically, without a build:

- `terminalSemanticLawCarrier_envelope_ge_erasureMoment_sub_failure` and
  `quittingSureBaseRoot_envelope_eq_max_prescribed_erasureMoment`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFixedLawCapRigidity.lean`).
- `quittingSureBaseRoot_unique_fixedLawDebtMinimizer_of_complement_solved`
  in that same file: its law is undated and its complement-solved/reverse-debt
  hypotheses are essential; it does not assert the unrestricted finite dated
  identification claimed here.
- `quittingTerminalErasureMoment_sub_failure_le_envelope`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalLawErasureDeviation.lean`).
- `quittingPunishmentValue`, `quittingPunishmentValue_eq_stationaryPunishmentValue`
  (`UniformEquilibrium/Quitting/Stationary/MinMax.lean`).
- `exists_quittingStationaryPunishmentRoot_lt_add` and
  `QuittingInstantPunishmentWorks`
  (`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`).

No claim that this package is absent everywhere in the codebase is made. A
bounded exact-symbol and hazard-reconstruction search did not locate the
finite dated-law fiber classification. No Lean files, exports, or shared
indexes were changed.
