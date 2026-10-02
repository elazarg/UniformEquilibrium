# No universal two-persistent-label exact-spine selector

Authors: ChatGPT External

Independent reviews:
[CODEX_ROOT review](../feedback/CHATGPT_EXTERNAL__PERSISTENT_TWO_LABEL_HAZARDS_SOLUTION__BY_CODEX_ROOT.md)

## Exact statement

Let `I` be a finite set with at least two elements, and fix a distinguished
player `o ∈ I`.  For every nonempty coalition `S ⊆ I`, define the reward
vector `r(S)` by

\[
r_o(S)=
\begin{cases}
0,&o\in S,\\
-1,&o\notin S,
\end{cases}
\qquad
r_j(S)=
\begin{cases}
-1,&o,j\in S,\\
0,&\text{otherwise}
\end{cases}
\quad(j\ne o).
\tag{1}
\]

At date `t`, let `x_t` be a product root: player `i` independently Quits with
probability `q_{t,i} ∈ [0,1]`.  A bounded exact Nash--Bellman spine consists
of values `v_t ∈ ℝ^I` and roots `x_t` such that, for every `t`,

1. `v_t` is the one-stage expected payoff obtained by executing `x_t`, using
   `v_{t+1}` if everyone Continues;
2. `x_t` is an exact Nash equilibrium of that one-stage continuation game;
   and
3. `|v_t(i)| ≤ 1` for every player and date.

Define the marginal Quit hazard of `i` at `t` to be `q_{t,i}`.  Then every
bounded exact Nash--Bellman spine for (1) satisfies

\[
\sum_{t=0}^{\infty}q_{t,j}<\infty
\qquad(j\ne o).
\tag{2}
\]

Consequently, no such spine has two distinct players whose marginal Quit
hazard series both diverge.

The conclusion also excludes both robust transports in
[`PERSISTENT_TWO_LABEL_HAZARDS.md`](../questions/PERSISTENT_TWO_LABEL_HAZARDS.md):
if two nominal nonnegative streams diverge, they cannot be transported to an
exact spine for (1) with either summable absolute loss on both labels or a
fixed positive fraction of both labels retained pointwise.

This is not caused by a lack of locally suitable roots.  For the four-player
instance `I={o,b,c,d}`, there is a sequence of exact Nash--Bellman edges whose
maximum marginal Quit probability tends to zero, whose two fixed marginal
labels `b,c` have divergent total nominal hazard, and whose joint and every
one-player-deleted absorption charges are positive at every edge.  These edges
cannot be concatenated while retaining nonsummable outsider charge on any
bounded exact spine.

## Conjecture-facing change

The question
[`PERSISTENT_TWO_LABEL_HAZARDS.md`](../questions/PERSISTENT_TWO_LABEL_HAZARDS.md)
asked for two persistent fixed labels on an exact bounded Nash--Bellman spine
for every finite reward table with at least two players.  The reward table
(1) refutes that universal quantifier.  The obstruction applies to every
bounded exact spine for the table, rather than merely exhibiting one badly
selected phantom spine.

The checked consumer
`nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine`
turns a two-persistent-label exact spine into the survival fields required by
chronological debt shadowing.  The result here proves that this sufficient
interface cannot be an unconditional selector for every reward table.

A viable replacement may be disjunctive, returning an already available
uniform-equilibrium certificate when one exists, or may restrict selection to
the positive-minimum-debt/no-equilibrium branch.  This packet proves neither
replacement and does not obstruct them.

## Definitions and semantic audit

The quitting game uses discrete dates.  At each live date, every player
simultaneously chooses Quit or Continue.  A product root means that the
players' randomizations at that date are independent.  If the set of Quitters
is nonempty, play stops and that exact coalition receives the terminal reward
vector (1).  If everyone Continues, the one-stage spine calculation uses the
displayed successor value `v_{t+1}`.

No public or private signal is introduced, and there is no correlated random
seed.  The root Nash condition permits one player to replace its entire
Bernoulli marginal by any other law on `{Continue, Quit}` while the opponents'
marginals remain fixed.  Because the player's payoff is affine in its own
Bernoulli law, checking the two pure endpoints is equivalent to checking all
such one-stage mixed deviations.

The all-spines theorem is an algebraic assertion about exact Nash--Bellman
spines.  It does not assume that the abstract successor values are the
terminal values of one executable infinite behavioral profile, and it does
not restrict an infinite-game deviator to a bounded controller.  Conversely,
it does not itself make a claim about the profitability of arbitrary
multi-date behavioral deviations.  Those deviations belong to the separate
downstream spine compiler.  This distinction prevents an abstract Bellman
spine from being silently identified with a terminal strategy profile.

The local packets below are individual exact Bellman-matched edges.  They are
not asserted to be one conditioned infinite chronology; the impossibility of
joining them with retained charge is precisely the point of the theorem.

## Proof of the all-spines obstruction

Fix an arbitrary bounded exact Nash--Bellman spine `(v_t,x_t)`.  Write

\[
p_t=q_{t,o},\qquad
\beta_t=\prod_{j\ne o}(1-q_{t,j}),\qquad
h_t=1-\beta_t,\qquad
z_t=v_t(o).
\tag{3}
\]

Thus `h_t` is the probability that at least one outsider Quits at date `t`,
or equivalently the owner-deleted opponent-clock charge.

The owner's pure-Quit endpoint is zero: every terminal coalition created by
that action contains `o`.  Exact root Nash and the Bellman mixture therefore
give

\[
z_t\ge0.
\tag{4}
\]

If the owner is forced to Continue, it receives `-1` when at least one
outsider Quits and receives `z_{t+1}` when every outsider Continues.  Its
pure-Continue endpoint is consequently

\[
C_t=\beta_tz_{t+1}-h_t
   =z_{t+1}-h_t(1+z_{t+1}).
\tag{5}
\]

Bellman evaluation of the owner's actual mixture gives

\[
z_t=(1-p_t)C_t.
\tag{6}
\]

We prove the pointwise potential inequality

\[
\boxed{h_t\le z_{t+1}-z_t.}
\tag{7}
\]

There are three exhaustive cases.

If `p_t=0`, the owner uses Continue surely.  Thus `z_t=C_t`; exact Nash also
gives `C_t≥0`, because the unused pure-Quit endpoint is zero.  From (5),

\[
z_{t+1}-z_t=h_t(1+z_{t+1})\ge h_t,
\]

where (4) at date `t+1` gives `z_{t+1}≥0`.

If `0<p_t<1`, both owner actions have positive probability.  Exact Nash
forces their endpoints to agree, so `C_t=0`.  Equation (6) gives `z_t=0`, and
(5) gives

\[
z_{t+1}=h_t(1+z_{t+1})\ge h_t.
\]

This identity also excludes any hidden division by a zero value of
`β_t`; no division has been used.

Finally, suppose `p_t=1`.  If an outsider `j` Quits, its payoff is `-1`,
because the terminal coalition contains both `o` and `j`.  If that outsider
instead Continues, its payoff is zero, regardless of which other outsiders
Quit, because the resulting coalition contains `o` but not `j`.  Any positive
Quit probability for `j` would therefore place positive weight on a strictly
inferior action and admit a profitable pure-Continue deviation.  Exact Nash
forces `q_{t,j}=0` for every outsider.  Hence `h_t=0`; equations (4) and (6)
then give (7).

Summing (7) on a finite window yields

\[
\sum_{t=m}^{n-1}h_t\le z_n-z_m\le1-z_m\le1.
\tag{8}
\]

The second inequality uses the actual canonical spine bound
`|z_n|≤1`, not a feasibility or terminal-law interpretation of `v_n`.
The nonnegative partial sums in (8) are uniformly bounded, so

\[
\sum_{t=0}^{\infty}h_t<\infty.
\tag{9}
\]

For every outsider `j`, the event that `j` Quits is contained in the event
that some outsider Quits.  Therefore `0≤q_{t,j}≤h_t`, and (9) proves (2).
Every pair of distinct players contains at least one outsider, so two
persistent marginal labels are impossible.

## Robust-transport consequence

Let `j≠o`, let `(q_{t,j})` be its actual summable stream on an exact spine,
and let `(\widehat q_t)` be a nonnegative nominal stream with divergent sum.

If

\[
\sum_t|q_{t,j}-\widehat q_t|<\infty,
\]

then

\[
\widehat q_t\le q_{t,j}+|q_{t,j}-\widehat q_t|
\]

would make the nominal stream summable, a contradiction.  If instead there
were a fixed `θ>0` with

\[
q_{t,j}\ge\theta\widehat q_t
\qquad\text{for every }t,
\]

then the actual stream would diverge, also a contradiction.  Every pair of
distinct labels includes an outsider, so both two-label robust transports are
excluded for this table.

## Boundary tests

### Exact stationary spine and terminal equilibrium

The obstruction is nonvacuous.  At every date, let the owner Quit surely,
every outsider Continue surely, and set `v_t=0`.  The owner is indifferent:
Quit pays zero, and Continue against all-Continuing outsiders returns the zero
successor value.  Every outsider strictly prefers Continue, which pays zero,
to joining the owner, which pays `-1`.  This is a bounded exact stationary
Nash--Bellman spine.  Its owner hazard diverges and every outsider hazard is
zero.

The same root at date zero is an exact terminal behavioral equilibrium.  Play
stops immediately.  An outsider can only lower its payoff by joining the
owner, while any multi-date deviation by the owner still yields zero against
outsiders who Continue forever.  Thus the table is not a counterexample to
uniform-equilibrium existence.

### Exact local two-label packets

Take four players `o,b,c,d`.  For a parameter `s∈(0,1)`, put

\[
\lambda=1-(1-s)^2=2s-s^2.
\tag{10}
\]

At one root, let `o,d` Continue surely and let `b,c` independently Quit with
probability `s`.  Take the successor vector `w` to be

\[
w(o)=\frac{\lambda}{1-\lambda},
\qquad w(b)=w(c)=w(d)=0.
\tag{11}
\]

The owner's pure-Quit endpoint is zero.  Its pure-Continue endpoint is

\[
(1-\lambda)\frac{\lambda}{1-\lambda}-\lambda=0.
\tag{12}
\]

For each of `b,c,d`, both pure endpoints are zero: `o` never belongs to a
current quitting coalition, and every non-owner successor coordinate is zero.
Hence the current value zero, the displayed root, and successor (11) form an
exact Nash--Bellman edge.

The joint absorption charge is `λ`.  If `h_{-i}` denotes the absorption
charge after deleting player `i`, direct product calculation gives

\[
h_{-b}=s,\qquad h_{-c}=s,\qquad
h_{-o}=\lambda,\qquad h_{-d}=\lambda.
\tag{13}
\]

Since `λ=s(2-s)≥s`, every one-player-deleted clock has exposure at least `s`.
Now choose the rational sequence

\[
s_n=\frac1{n+4},
\qquad
\lambda_n=2s_n-s_n^2.
\tag{14}
\]

The maximum marginal Quit probability at the `n`th root is `s_n`, hence tends
to zero.  Both fixed nominal labels `b,c` have divergent hazard sum
`\sum_ns_n`, every deleted clock has positive exposure, and the successor
vectors tend to zero.  Moreover `s_n≤1/4`, so
`w_n(o)=\lambda_n/(1-\lambda_n)≤7/9<1`; the local predecessor and successor
both lie in the canonical reward box.  All Nash and Bellman defects remain
exactly zero.

This is the positive local boundary test requested by the question.  It does
not contradict (2), because the successor (11) of one edge is not the zero
predecessor of the next.  Any attempt to place nonsummably many of these
outsider charges on one bounded exact spine would make (8) force an unbounded
increase in the owner's coordinate.  Thus the obstruction is chronological,
not a failure to find two active labels in fine local packets.

### Cardinality and degenerate-root checks

The all-spines proof works already for two players: there is then one owner
and one outsider, and every distinct pair contains that outsider.  Four
players are used only for the symmetric local test with two displayed
outsider labels and two inactive labels.

The proof also covers sure actions.  The cases `p_t=0` and `p_t=1` were not
discarded by an interiority assumption.  In particular, the `p_t=1` argument
forces `h_t=0`, while the mixed-owner identity remains valid even if
`β_t=0`.  These are the singular boundaries at which a likelihood-ratio or
division-based proof could otherwise fail.

## Source correspondence and novelty audit

The project representation agrees with the definitions above as follows.

- `IsCanonicalExactQuittingNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`
  packages the bound, exact Bellman recursion, and exact root Nash conditions
  used here.  Its bound is
  `|value time who| ≤ quittingRewardBound reward`; for (1), that reward bound
  is exactly one.
- `IsεQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/FirstBranch.lean` quantifies over every
  replacement PMF on `Bool`, matching the unilateral root-deviation audit
  above.
- `quittingRootSuccessorPayoff_eq_endpointMix` and
  `isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean` identify the
  Bellman mixture and justify the pure-endpoint support calculations.
- `quittingRootSuccessorPayoff_eq_max_endpoints_of_endpointNash` and the
  deleted pure-Continue formula in
  `UniformEquilibrium/Quitting/Cycles/CycleMismatchContraction.lean` provide
  the nearby checked endpoint algebra.
- `quittingOpponentClockCharge` in
  `UniformEquilibrium/Quitting/Paths/OpponentClockDichotomy.lean` is the
  quantity `h_t` in (3).
- `quittingMarginalQuitHazard_le_opponentClockCharge`,
  `summable_quittingOpponentClockCharge_iff`, and
  `hasTwoPersistentQuittingMarginals_iff_all_suffix_survival_zero` in
  `UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`
  provide the checked marginal/deleted-clock translation and downstream
  survival interpretation.
- `nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/NashBellmanChronologicalForcing.lean`
  is the named consumer whose universal two-label input is refuted.

The canonical all-Continue phantom-spine regression in
`NashBellmanClockReduction.lean` proves that a bad exact spine exists for
every reward table.  It does not prove that one table forbids two persistent
labels on every exact spine.  The summable-clock result in
`UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean` uses
additional dynamic-debt and punishment-floor hypotheses and does not subsume
the table-specific potential (7).  A narrow declaration and phrase search in
these files found no theorem implying (7) or (2) for all spines of a fixed
reward table.

No literature theorem is used or translated in this proof.  The construction
was produced directly in response to the project question, so there is no
paper hypothesis or probability convention to reconcile.  The novelty claim
is only relative to the inspected project declarations, not a claim of
priority in the external literature.

## Adapter and consumer

The actual-data adapter is direct: choose any finite player type with at least
two elements and an owner, instantiate the reward function by (1), and supply
any value/root pair satisfying
`IsCanonicalExactQuittingNashBellmanSpine`.  Inequality (7) then converts the
owner-deleted root charge into increments of the bounded scalar potential
`v_t(o)`.  Summation and marginal event inclusion return (2), and the checked
definition `HasTwoPersistentQuittingMarginals` is therefore false.

This strictly closes the universally quantified question negatively.  It
does not feed a positive survival certificate to the chronological consumer;
instead, it proves that the consumer's proposed universal producer cannot
exist.  The local packet construction shows that adding the currently
available finite packet exposures does not repair that producer without a
new chronological or branch restriction.

## Lean handoff

The narrow formalization target is a new counterexample file importing the
exact-spine definition, endpoint algebra, and persistent-label definitions.
Suggested declarations are:

1. `oneOwnerHazardObstructionReward`, implementing (1), followed by exact
   simplification lemmas for the owner Quit endpoint, owner Continue endpoint,
   and outsider endpoints when the owner Quits surely;
2. `ownerDeletedCharge_le_value_succ_sub_value_of_exactSpine`, formalizing
   (7) by cases on the owner's Quit probability;
3. `summable_marginalQuitHazard_outsider_of_exactSpine`, deriving (2) from the
   canonical bound and marginal event inclusion;
4. `not_hasTwoPersistentQuittingMarginals_oneOwnerReward`, the principal
   negative result; and
5. an optional `Fin 4` local-packet namespace proving (10)--(14) and the four
   exact deleted-clock identities (13).

Useful existing lemmas include
`isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash`,
`quittingRootSuccessorPayoff_eq_endpointMix`,
`quittingMarginalQuitHazard_le_opponentClockCharge`, and the pointwise bound
field of `IsCanonicalExactQuittingNashBellmanSpine`.  The summability proof
should be built from the finite-window telescope (8); it should not assume
summability as a certificate field or invoke the desired two-label negation.

For the local test, the rational parametrization (14) avoids formalizing a
square-root inverse.  Finite tests should include `p=0`, `p=1`, a mixed owner,
and each of the four deleted labels.  No new structure should contain (7),
(2), or the final negation as an assumed field.

## Scope and nonclaims

This result does not disprove the finite-quitting uniform-equilibrium
conjecture.  The displayed game has an exact immediate-exit equilibrium.

It does not refute a producer restricted to positive minimum terminal debt,
positive-gap tangent data, or the no-uniform-equilibrium branch.  It also does
not refute a disjunctive procedure allowed to return an existing equilibrium
instead of a two-label spine.

The local packets are not one executable infinite strategy and are not
claimed to preserve semantic sources under conditioning.  They show only
that exact local Nash--Bellman matching, vanishing root probabilities, two
fixed local labels, and all one-player-deleted exposures do not overcome the
global bounded-potential obstruction.
