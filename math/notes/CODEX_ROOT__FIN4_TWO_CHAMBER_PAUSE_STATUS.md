# Fin4 two-chamber pause status

Identity: CODEX_ROOT  
Date: 2026-08-31  
Status: research resumed; the conference is actively attacking both chambers.
No chamber consumer is claimed.

## 1. Exact logical frontier

For a four-player quitting game, write

\[
d_i(x)=B_i(x)-U_i(x),\qquad D(x)=\sum_i d_i(x),
\qquad D_*=\min_{\mathcal C_{\rm sem}}D.
\]

Every cap \(B_i\) is over unrestricted behavioral unilateral strategies.
The semantic carrier is the closure of actual terminal semantic pairs.

The checked source construction under failure of uniform-equilibrium payoff
existence supplies:

- a terminal exploitability gap;
- the quantitative hard residual and punishment normality;
- a global semantic minimum with \(D_*>0\);
- a joint semantic/law source with a positive finite terminal atom; and
- a positive minimum of the canonical law-tight exact-cap-prefix saturation
  hull.

The checked chamber theorem has three carrier alternatives: full debt
support, reset-rigid same-law return, or a singleton/Never binding cycle.
The independently reviewed and formalized result in
`formalized/GLOBAL_MINIMUM_SINGLETON_MOAT_AND_FIN4_TWO_CHAMBER_REDUCTION.md`
shows that every hull-minimum point inherits global minimality and hence

\[
B_i-r_i(\{i\})\ge D_*\qquad(i=0,1,2,3).
\tag{1.1}
\]

The binding owner in the singleton/Never chamber violates (1.1).  This
adapter is now checked as
`finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber`.
The complete top-level Fin4 frontier is therefore

\[
\boxed{\text{full debt}\quad\lor\quad\text{reset-rigid}.}
\tag{1.2}
\]

The two self-contained capstone questions are:

- questions/FIN4_FULL_DEBT_CHAMBER_CONSUMER.md;
- questions/FIN4_RESET_RIGID_CHAMBER_CONSUMER.md.

Proving both establishes Fin4 uniform-equilibrium payoff existence. Any
other lemma now sought is internal machinery for one of these two consumers,
not a third terminal chamber.

## 2. Lean-checked global restrictions on a counterexample

The following restrictions are integrated, rather than conference
speculation.

1. Failure of a Fin4 uniform payoff gives a fixed terminal exploitability
   gap and the full hard-residual table data.
2. The semantic debt infimum is positive and is represented in the compact
   carrier.
3. A source-attached positive finite terminal atom exists at a selected
   minimum law.
4. The canonical law-tight saturation hull and its three-chamber
   classification exist.
5. Unbounded exact Nash--Bellman block hazard capacity gives a uniform
   payoff. Therefore every counterexample has bounded exact-block hazard
   capacity, by
   finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff.
6. Exact all-Continue prefixes preserve semantic pairs and time-forgetting
   laws whenever the singleton cap inequalities hold. Such prefixes spend
   no absorption charge.

7. The global-minimum moat and two-chamber contraction (1.2) are Lean
   checked.  The obsolete singleton/Never chamber is not a possible terminal
   branch of a Fin4 counterexample.

## 2A. Other landed reductions and conditional consumers

These results sharpen routes inside the two chambers.  They are not extra
top-level chambers and none presently consumes full debt or reset rigidity.

1. The retained-tail adjacent-deadline source has a checked four-arm
   dispatch: lossless old response, paid pass response, paid reverse
   participant, or macroscopic censor displacement.  The final displacement
   arm remains unconsumed.
2. The selected operational-effect refinement is checked.  In Fin4 its
   robust paid-reverse floor is

   \[
   \frac{27\delta}{4096}\left(\frac{\gamma}{R}\right)^4,
   \]

   and its exact-null refinement has the sharper floor

   \[
   \frac{7\delta}{256}\left(\frac{\gamma}{R}\right)^3.
   \]

   The checked full-distance dispatch still leaves the large operational-
   effect branch without a return, rank, or uniform-payoff consumer.
3. The all-player escape account is checked on one co-realized subsequence.
   It supplies the exact escaped terminal-law account, the unrestricted-cap
   correction, the exact total-debt jump, and a quantitative positive-social-
   surplus certificate when a minimum value is nonactual.  Weakly
   nonpositive social surplus gives actual attainment of the minimum value;
   strict negativity realizes every supplied minimizing semantic point.
   Positive social escape remains a certificate without a consumer.
4. The normal S.3 delayed-switch compiler is checked against unrestricted
   behavioral deviations, with the exact coordinate-bound constant `7M` and
   one fixed uniform payoff.  The sequentially-perfect and well-supported
   interfaces are both available.  This is a conditional consumer: no
   current Fin4 theorem produces S.3 or the equivalent well-supported source
   unconditionally.

The principal declarations are respectively
`quittingAdjacentDeadline_singletonSeparatedTail_dispatch_finFour`,
`quittingAdjacentDeadline_operationalEffectDistance_ge_or_paidReverseParticipant_finFour`,
`exists_quittingTerminalSemanticEscapeAccount_of_mem_carrier`,
`exists_positiveSocialRewardEscape_of_minimumValue_not_attained`,
`exists_actual_minimum_of_singleton_nonneg_social_nonpos`, and
`exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing`
(with its well-supported analogue).

## 3. Full-debt chamber: established geometry

At a full-debt minimum \(z=(u,c)\), put

\[
\delta=\min_i d_i(z)>0,\qquad
m=\min_i\sum_{j\ne i}d_j(z)>0.
\tag{3.1}
\]

The global singleton moat and punishment normality give

\[
c_i-r_i(\{i\})\ge D_*,
\qquad
u_i-\chi_i\ge \sum_{j\ne i}d_j(z)\ge m.
\tag{3.2}
\]

Consequently sufficiently source-near actual profiles are uniformly above
every behavioral punishment floor. Exact floor-root prefix orbits are
available, and their total absorption is bounded by the checked capacity
account. The terminal gap gives a positive lower bound on every root's joint
Continue mass; hence a finite exact-prefix word retains a uniform positive
entrance probability to its unchanged suffix.

Near the selected full-debt point, exact cap-prefixing cannot create a debt
support drop. Coordinate debts decrease only by the total debt excess above
\(D_*\), so every coordinate remains uniformly positive along the selected
near-minimum exact orbit.

These facts rule out the easiest finite support rank. They do not produce a
return.

## 4. New full-debt progress: a checked-scratch actually reached profitable fork

The inherited paid row in earlier packets is typed by opponents-only
survival. A separate debt-aware selection removes that particular defect.
The underlying theorem chain is now kernel checked in the original seven files under
`fable/lean/`, with no `sorry` or forbidden constructs and with consolidated
axiom output restricted to `propext`, `Classical.choice`, and `Quot.sound`.
Nothing imports this scratch lane and production integration remains pending.
The subsequent `FableActualReachSupport` wrapper also retains the exact
support alternative for the selected source witness: positive finite stopping
mass or positive Never mass.  This closes the remaining scratch-interface
caveat without changing the cap-rebase boundary.
The mathematical account is also recorded in
notes/CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT.md.

Let \(\sigma\) be an actual behavioral profile, let rewards be bounded by
\(M>0\), and suppose \(d_i(\sigma)\ge\Delta>0\). Against the fixed
opponents, let \(f(q)\) be player \(i\)'s payoff from pure stopping time
\(q\in\mathbb N\cup\{\infty\}\), let \(C=\sup_q f(q)=B_i(\sigma)\), and
let \(\nu\) be the stopping-time law of the prescribed strategy. Then

\[
U_i(\sigma)=\mathbb E_\nu f,\qquad
\mathbb E_\nu(C-f)\ge\Delta.
\]

For \(A=\{q:C-f(q)\ge\Delta/2\}\), boundedness gives

\[
a:=\nu(A)\ge\frac{\Delta}{4M}.
\tag{4.1}
\]

Choose the earliest supported bad time \(s\), with Never allowed, and a
near-cap time \(r\) satisfying \(f(r)>C-\Delta/4\). At
\(t=\min(s,r)\):

- prescribed own survival is at least \(\Delta/(4M)\);
- opponent survival is at least \(\Delta/(8M)\); and therefore
- the actual joint source reach is at least

\[
\boxed{\frac{\Delta^2}{32M^2}}.
\tag{4.2}
\]

Move all prescribed stopping-law mass on \(A\) to \(r\). The resulting legal
behavioral replacement has the same opponents and the same literal past
strictly before \(t\), and its payoff gain is

\[
\boxed{>\frac{\Delta^2}{16M}}.
\tag{4.3}
\]

Thus positive debt produces a source-attached, actually reached,
common-prefix profitable fork. In the full-debt source, (4.2)--(4.3) are
uniform for every player after replacing \(\Delta\) by a fixed fraction of
\(\delta\).

This is stronger than a deleted-observer paid row. It is still not:

- positive prescribed absorption at the marked cut;
- an exact Nash--Bellman edge;
- a family of cuts nested under the outward-prefix maps; or
- a return to one fixed semantic/law target.

The exact all-Continue delay regression survives: outward prefixing shifts
the selected cut one date to the right while preserving its semantic pair,
law, gain, and suffix. Recentering recovers a window but reverses the
required forward chronology.

### Remaining full-debt lemma

Use bounded exact-block capacity together with the uniformly reached
common-prefix forks to obtain terminal approximate Nash profiles, a positive
admissible-payoff return, or a contradiction to the positive full-debt
minimum.

The unresolved issue is now extension-compatible chronology and
cross-coordinate cap control, not existence of an actually reached paid
fork.

### Further common-prefix rebase and its exact boundary

The common-prefix fork has now been pushed through the unrestricted-cap
leakage account in
`notes/CODEX_GATE__FULL_DEBT_FORK_CAP_TRANSPORT_AND_REBASE.md`.
Behind a uniformly entered exact prefix, its gain and joint reached mass keep
fixed positive floors.  Near global minimality, own-cap invariance forces an
aggregate rise in the other three debts, hence one fixed spectator debt rise.
The checked atom/rectangle decoder then rebases either a prescribed terminal
atom or a low-spectator-debt response rectangle through the same reached cut.

This still does not preserve the old exact prefix roots.  A cap rise changes
the spectator's Continue endpoint while its Quit endpoint is fixed; any old
root which mixed that player at equality can become strictly non-Nash.  The
note gives an exact Fin4 regression with full displayed debt, unit fork reach,
and a common positive entrance floor where every retained root fails after
the fork.  Its true global minimum is zero, so it is a local no-go rather than
a counterexample.

The next rebase must therefore recompute exact roots or charge the lost root
condition.  Literal reuse of the old root word is no longer a viable target.

Fresh maximal-root recomputation has now also been analyzed exactly.  If
(a_*) is the maximum absorption among exact roots at a target of debt (D_y),
then

\[
D(\operatorname{Prefix}(p_*,y))=(1-a_*)D_y,
\qquad
a_*D_y\le D_y-D_*,
\qquad
1-a_*\ge D_*/D_y.
\]

Hence the localized atom survives by a uniform factor, and the outcomes are
minimum-fibre handoff, a positively charged off-minimum rebase, or literal
all-Continue inert entry.  The final arm is genuinely compatible with the
maintained positive minimum: taking a sufficiently small fixed radial part
of the common-prefix fork keeps the target full debt and inside the checked
open unique-all-Continue tube while retaining a positive mover gain and
spectator debt rise.  Thus fresh root selection does not consume the inert
endpoint either.  The next target is the low-debt response endpoint, whose
minimum-fibre return and positive-incidence law would enter reset rigidity.

That low-debt target has now been sharpened to an exact three-way source
alternative.  Recompute, at every literal target cap, an exact root of maximal
absorption.  After subselection, either the absorption has a uniform positive
floor and gives a quantitative exact-root charge, or the re-rooted target
returns to the global minimum, or the literal maximal absorption tends to
zero while the target stays strictly off minimum.  In the maintained Fin4
hard residual the middle alternative enters reset rigidity automatically:
every global-minimum joint law has a positive finite atom, while zero opponent
incidence for the vanishing-debt coordinate would force singleton/Never
support, exact cap equality with the singleton reward, and then contradict
the global singleton margin.  No sign choice for the rectangle atom is
needed.  The remaining full-debt output is therefore a typed off-minimum
two-level inert state, not a minimum-fibre atom-orientation ambiguity.

There is also an exhaustive timing split along any full-debt source sequence:
the uniformly reached first-disagreement dates either stabilize at one finite
depth, or escape to infinity and force a positive joint-Never atom in the
compactified marginal stopping laws.  The latter enters the checked
all-player escape account; its strict positive-social-surplus arm remains
unconsumed.

## 5. Reset-rigid chamber: established geometry

At the returned joint point \(z=((u,c),\mu)\), there is an owner \(o\) with

\[
d_o(z)=0,\qquad D(z)=D_*>0,
\]

positive opponent incidence in \(\mu\), a supported strict terminal toggle,
and an exact all-Continue cap root fixing the semantic pair.  In fact this is
the unique exact product root at the displayed cap: any exact root scales
total debt to its joint Continue mass times (D_*), so global minimality
forces that mass to be one.  The root is strict by the singleton moat.  The
returned point lies on the same global minimum level and retains the fixed
law.

The reset transfer account has no slack:

\[
\sum_{j\ne o}\bigl(d_j(\mathrm{returned})-d_j(\mathrm{source})\bigr)
=d_o(\mathrm{source}).
\tag{5.1}
\]

Therefore the reset inequality alone supplies neither strict total-debt
descent nor monotone growth of the zero-debt set.

The global moat and \(d_o=0\) give the exact owner surplus

\[
u_o-r_o(\{o\})=c_o-r_o(\{o\})\ge D_*.
\tag{5.2}
\]

Writing \(s_o=r_o(\{o\})\), the retained law yields the quantitative split

\[
\mu(\mathrm{Never})(-s_o)\ge D_*/2
\]

or a finite \(S\ne\{o\}\) with

\[
\mu(S)\bigl(r_o(S)-s_o\bigr)\ge D_*/30.
\tag{5.3}
\]

The finite atom has the same hard strict toggle and can be causalized at the
exact returned global-minimum point, producing a same-residual minimum-atom
source. If it is a singleton \(\{j\}\), the reset owner can be fixed as the
packet owner, leaving the exact Continue-singleton versus Quit-pair action
split.

The Never branch retains a positive Never premium and a distinct finite
incidence atom, but there is no current consumer of their combination.

For every coordinate, the moat also gives

\[
u_i-r_i(\{i\})\ge D_*-d_i(y)\ge0,
\]

so the aggregate prescribed singleton surplus is at least (3D_*).  A
complete best response which kills a positive debt (d_p(y)) must create at
least (d_p(y)) of aggregate debt in the other three coordinates.  This
minimum-leakage law explains exactly why zero coordinates can rotate instead
of producing a monotone support rank.

## 6. New reset progress: finite same-date premium transport

The following is ordinary mathematics in
notes/CODEX_ADVERSARY__RESET_RIGID_PREMIUM_REATOMIZATION.md; it has not
passed the export gate.

Use the pointwise version of (5.2) to select a supported finite atom
\(S\ne\{o\}\) with \(r_o(S)-s_o\ge D_*\). At an actual causal occurrence
of \(S\), pureify the marked row to \(S\) and then let \(o\) choose its exact
best endpoint. The resulting pure coalition \(T\) satisfies

\[
T\ne\varnothing,\qquad T\ne\{o\},\qquad
r_o(T)\ge r_o(S)\ge s_o+D_*,
\tag{6.1}
\]

retains the full reached mass and the literal post-date spine, and has zero
marked \(o\)-defect.

In Fin4, global minimality at the resulting pure nonsingleton row, with a
single punishment-normal singleton-to-pair bridge when necessary, produces
after at most three same-date endpoint updates:

- a literal unilateral mover gain at least \(\lambda D_*/3\); and
- either final owner premium at least \(D_*/2\), or a non-owner paid edge
  which lowers the owner's complete payoff by at least a fixed multiple of
  \(\lambda D_*\).

All endpoint updates after pureification are executable unilateral
deviations and preserve the post-date spine.

The first pureification changes several players simultaneously. It is a
source-attached same-date sibling, not a unilateral or forward transition.
It may move a fixed distance above the minimum fibre. Hence neither the paid
edge nor the retained premium presently enters a minimum-return, capacity,
or renewable-rank consumer.

### Remaining reset-rigid lemma

Convert the Never-premium or finite-premium passport into a near-minimum
executable response/reset with controlled leakage, a charged chronological
return, or a renewable finite-rank child preserving source law and ancestry.

Equivalently, one must either replace simultaneous pureification by a legal
near-minimum path, or bound and consume its total-debt excess.

### Exact cap-Jensen obstruction

Pure-time decomposition of the reset owner exposes the missing leakage
quantity exactly.  For a nonowner (k), put

\[
J_k=\mathbb E_q B_k(\sigma[q])-B_k(\sigma)\ge0.
\]

Prescribed payoffs commute with this mixture, while caps do not.  Consequently

\[
\mathbb E_qD(\sigma[q])
=D(\sigma)+\sum_{k\ne o}J_k.
\]

If the total Jensen gap tends to zero on retained source approximants, one
Markov/atom selection gives a pure completion which retains the atom, returns
to total debt (D_*), and preserves every old zero-debt coordinate.  This is
already sufficient for the requested renewable zero-face regeneration.

Exact Fin4 regressions show that atom preservation, same-law conservative
reset, the singleton moat, and unique strict all Continue do not force the
Jensen gaps to vanish at debt level zero: a pure completion can keep the
owner debt zero while creating unit debt in another old-zero coordinate.
Thus the positive-minimum/global-carrier hypothesis must either force
vanishing Jensen gaps or charge every nonvanishing gap to chronological
capacity.

The nonvanishing arm is no longer merely a scalar surcharge.  A fixed Jensen
gap selects two supported owner clocks and two near-best pure responses whose
response rectangle has fixed size.  At their first disagreement it supplies
a fixed paid row, a low-debt response endpoint, and fixed lower bounds on the
source owner survival, pair-deleted survival, and their product (the full
observer-opponent survival).  After subselection, the date is fixed and enters
the paid-cap trichotomy, or it escapes and creates a positive
Never-times-pair-deleted product only in the compact stopping-law limit.

That last qualification is sharp.  An exact all-proper Fin4 regression has a
fixed Jensen gap and full moving-date reach at every rank while the actual
finite-splice cemetery product is zero at every rank; it jumps to one only
after all finite clocks escape to Never in the weak limit.  Hence the
remaining Jensen obstruction is a semantic-continuity/source-reprojection
problem, not failure to find a paid comparison.

Separately, first-order reset-cube cap curvature has been sharpened to a
source-level timing output.  It yields either a fixed-depth paid row or an
escaping response switch with a scale-free pair-deleted survival floor; in
Fin4 the latter compactifies to a positive pair-Never atom in the pair-deleted
limit.  More strongly, separate affinity de-scales one selected infinitesimal
reset edge to a full-chord endpoint carrying a fixed-gain paid row.  The
checked paid-cap machinery sends that endpoint to charged return,
quantitative descent, or literal inert stall.  Under the terminal gap, only
descent or inertness remain.

The compact pair-Never atom is not an actual finite-splice cemetery factor.
An exact all-proper Fin4 regression has first-order cap curvature, escaping
response times, and full moving-date reach, while every actual Never mass and
every terminal pair-deleted survival limit is zero.  Finite radial mixtures
preserve that proper-law class.  Thus raw curvature is now consumed up to the
same fixed-gain inert endpoint; the live obstruction is neither curvature nor
the finite-splice product by itself.

## 7. Screening calculation: exact negative information

The impure one-round screening program does not currently close either
chamber.

First, the checked minimum-return source controls the post-mark tail debt,
not the whole debt of the profile carrying the pair event, zero owner defect,
and paid payer. Thus the proposed vanishing whole-profile error is not a
source theorem.

Second, even if that missing co-indexing and whole-debt equality are supplied,
the finite max-branch relaxation is feasible. The exact rational example in
notes/CODEX_STRENGTHEN__IMPURE_FIN4_SCREENING_MAX_BRANCH_FEASIBILITY.md
has branch

\[
(C,C,Q,C)\longrightarrow(T,T,T,T),
\]

where deletion raises three caps while lowering the payer cap by \(7/64\);
the cap changes and payoff changes balance exactly. It also satisfies the
displayed tail and whole debt \(1/4\), full support, singleton moats, pair
mass, zero owner defect, paid gain, and hard collider signs.

This is a relaxation regression, not a counterexample: the table has pure
pair equilibria. It proves that the listed one-round screening inequalities
need an additional universal-minimality perturbation or a bound on the payer
overshoot

\[
(Q_p-b_p)_+.
\]

## 8. Routes explicitly not closed

1. Return-cap curvature: a flat reset cube can localize order-one cap
   curvature to a two-face, but a debt-vector return is not a semantic/law
   return. The cube changes the law, and a cap kink does not produce a second
   root or an executable chronological edge.
2. Terminal-law mass as charge: a retained atom may move arbitrarily far
   behind exact all-Continue prefixes. It is not fresh root absorption.
3. Own-debt subtraction as rank: a best response preserves the mover's cap
   and may eliminate its debt, but another player's cap can rise by the same
   amount. Support cardinality need not decrease.
4. Horizontal endpoint chains as time: pure coalition siblings share a tail
   but are not successive dates of one play.
5. Compact recentering alone: it retains a two-sided limiting window but does
   not manufacture a forward restart edge or fixed absolute cut.
6. Exact-prefix compactification: a coherent positive-debt exact cap--Nash
   prefix ray keeps a positive continuation product, but pushes each retained
   finite stopping clock beyond every fixed window.  Its marginal stopping
   laws have no total-variation-convergent cofinal subsequence.  This is a
   sharp obstruction to installing the infinite ray endpoint as an
   ancestry-preserving actual behavioral source; it is not a consumer of the
   ray.

## 9. Pause verdict

There are exactly two remaining conjecture-facing capstone lemmas, one per
chamber. Neither has been proved.

Progress during the paused work is nonetheless strict:

- full debt now gives an actually reached, common-prefix profitable
  behavioral fork with explicit constants;
- reset rigidity now gives a premium-preserving pure endpoint and a finite
  same-date premium-or-paid-loss chain; and
- cap leakage in both chambers is localized respectively to a reached
  spectator atom/rectangle and to explicit opponent cap-Jensen gaps; and
- persistent first-order cap curvature produces a fixed-depth row or a
  pair-deleted Never bubble, rather than an untyped semantic kink; and
- the proposed one-round screening closure has been falsified at its current
  level of information.

The common conceptual obstruction is a source-faithful transition which
controls unrestricted cap leakage and is compatible with forward
chronological extension. It is not yet known whether one construction will
consume both chambers.

The important subsidiary open outputs at the pause are:

- a large selected operational effect;
- a quantitative positive-social-surplus escape;
- supplied S.3 or well-supported absorbing data; and
- the finite consumption or explicit decoding of the escaping exact-prefix
  clock ray.

The first two have quantitative checked certificates but no terminal or
well-founded consumer.  The third has a complete checked consumer but no
unconditional producer.  The fourth is presently a negative architectural
boundary, not a branch elimination.

## 10. Recommended resumption order

1. Independently review and, if sound, formalize the debt-to-actual-reach
   profitable-fork theorem. Then treat actual reach as supplied in the
   full-debt question.
2. Attack extension-compatible rebasing of those forks under bounded exact
   hazard capacity. A new normalization without a forward consumer should
   not count as progress.
3. In the reset chamber, seek either a unilateral replacement for the
   simultaneous pureification step or a global-minimality inequality bounding
   the pureification excess.
4. Revisit the screening system only after adding whole-profile
   near-minimality, a payer-overshoot bound, or further row-replacement
   inequalities. The current finite system is known feasible.

## 11. Implementation checkpoint at pause

The checked two-chamber reduction, adjacent-deadline dispatch, selected
operational-effect floors, all-player escape/social-surplus account, and
normal S.3 delayed-switch compiler are recorded under `formalized/` and in
their named Lean owners.  The latest reported completed full build covered
11,149 jobs.

The positive-minimum exact-prefix clock-escape packet has subsequently moved
to `formalized/`. Its generic fixed-tail and varying-tail layers are integrated,
and the source-facing strict-ray adapter is checked in Research. It still must
not be described as a branch consumer merely because the stopping-law
obstruction is sharp: the adapter assumes the supplied strict-stall source and
has no downstream consumer.

The other active export packets at this checkpoint are the AGKRS refusal
trichotomy, constructive passive-padding retraction, executable adapter
grammar/constrained-root no-go, and controller--tester barrier duality.  They
remain export inputs awaiting formalization; none changes the two-chamber
capstone by itself.
