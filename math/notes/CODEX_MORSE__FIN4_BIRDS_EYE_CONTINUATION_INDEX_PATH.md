# Fin4 bird's-eye path: close continuation prices before choosing clocks

Owner: CODEX_MORSE.

Status: an INTUITION-LEVEL PROOF PROGRAM, not a proof, producer theorem,
counterexample-class reduction, or export candidate. The requested result
is UE for EVERY four-player reward table, against EVERY behavioral
deviation. The argument below identifies one main global mechanism and
three substantial unproved bridges. It does not count those bridges as
supplied inputs or already available theorems.

## 1. The central picture

My best current intuition is this:

> The equilibrium is a self-financing circuit of continuation prices,
> not necessarily an improving sequence of existing strategy profiles.
> Construct the whole circuit first. Only then implement its clocks.

One player's profitable timing change can create another player's
profitable timing change. The difficulty is not absence of a response;
it is that the unpaid obligation moves. A source-minimum repair tries
to make that moving obligation disappear immediately. I now think the
more persuasive global attempt is to let obligations pass through a
whole Nash-continuation diagram until they close consistently. On a
closed diagram, everyone compares Quit with the SAME future that the
construction will actually supply. There is no spectator cap left
outside the accounting.

There are two genuine kinds of motion in this diagram:

- slow one-owner hazard blocks, which implement continuous singleton
  payoff arcs and can be refined without changing their target;
- actual independent product-root jumps, which keep macroscopic
  simultaneous quitting rather than replacing it by an average.

Both are needed. The first can turn a pure response cycle into a proper
growing-clock equilibrium. The second can cross a collision trap that
no singleton-only motion handles. Their endpoints must be the SAME
continuation ports. A mixture of two different future payoff targets
is not itself a future strategy in this game.

The proposed existence principle is topological, but not the generic
claim that every face has an escape. It is a game-specific **index
conservation law for the entire decorated Nash-continuation graph**.
An essential equilibrium branch should either finish at a correctly
punishment-priced absorbing root or continue through the collision
and singleton strata. If no finishing branch exists, the branch must
support arbitrarily much physical absorption inside a bounded payoff
box. Existing compilers then give approximate equilibria.

This is the place where I would put the main proof effort. It is NOT
proved that an essential branch survives, carries positive charge, or
has the required global index. Those are the hard bridges below.

## 2. What the existing mathematics does and does not settle

The original problem has sixty signed finite-coalition rewards, four
independent private clocks on ℕ∪{Never}, and zero live/Never rewards.
The selecting live date pays zero; the absorbing reward starts later.
Before absorption there is only one public history. A deviator may
replace its entire clock, including every late finite date and Never.

For a profile p let U be prescribed payoffs, B the complete caps,
d_i=B_i−U_i≥0, D=Σ_i d_i, and E=max_i d_i. Terminal approximate Nash
profiles at every error are exactly enough for one FIXED uniform
equilibrium payoff target. It is unnecessary to prescribe that target
before searching for the profiles; compact payoff selection does that
afterwards. It is necessary to retain the target before the accuracy
in the final UE conclusion.

The existing positive results cover three broad ways an equilibrium
can already be found: a suitable absorbing anchor/base with a true
punishment tail; a stationary or small-hazard matrix/index source; or
a coherent multi-phase singleton/collision construction. Raw leaver,
weighted-floor, boxed-charge, matching, triple, cyclic, inverse and
quotient criteria cover many signed tables. They do not exhaust the
sixty-dimensional table space. In particular, a remaining standard-Q,
degree1 full-core table need not fail UE, and absence of a pure terminal
Nash coalition says little about long clocks.

The strongest reviewed counterexample source is much more precise.
If any Fin4 counterexample exists, one can select ONE fresh table with
positive own singleton rewards and

    0<δ=Δ_all<Δ_abs=δ+g,       g>0.

Every full-carrier minimum has one common debt vector, all four of
whose coordinates are positive. All four Never masses are positive.
The first prescribed stage is a random nonsure collision. A paid
owner ties a first and a later FINITE cap, with different payoff
kernels on a positive opponent event. Repeating the source block
honestly raises a conditional-Never cap. This is reviewed ordinary
mathematics, not the missing UE consumer.

The full NP statement is not being called Lean-checked. Recipient
scaling and the fresh contact/common-debt producer now have production
declarations, but they select a new table before ALL its new minima;
they do not transport old minimizing profiles to that table.

Why not simply prefix this minimum by an equilibrium root? A root
that is Nash against its FULL old cap vector would scale all debts
by joint survival c. If c<1, that would contradict positive global
minimality. Hence the minimum only admits the neutral such prefix.
The prospective equilibrium has to be built elsewhere. Its continuation
prices are not silently identified with the minimum's U or B.

## 3. The concrete object to build

Fix ONE table r, own rewards s_i=r_i({i}), reward bound M, and a
fixed payoff box K=[−M−2,M+2]⁴. For an independent root q∈[0,1]⁴
write c(q)=∏_i(1−q_i), a(q)=1−c(q), and

    F_i(v,q)=Σ[S≠∅]Pr_q(S)r_i(S)+c(q)v_i.

Here v is the all-Continue continuation PRICE. The two endpoint
values for owner i are

    Q_i(q)=Σ[A⊆I\{i}]Pr_{q_-i}(A)r_i(A∪{i}),
    C_i(v,q)=Σ[A≠∅]Pr_{q_-i}(A)r_i(A)+χ_i(q)v_i,
    χ_i(q)=∏[j≠i](1−q_j).

An exact root is Nash if its Bernoulli coin assigns mass only to
maximizing endpoints. Equivalently, the stage regret

    e_i(v,q)=max(Q_i(q),C_i(v,q))−F_i(v,q)

is zero for every i. The full decorated root graph keeps (v,q,F(v,q)),
not just its projected successor-payoff set. No convex hull of possible
successor payoffs is taken.

The sought global output is a finite root word with annotations
v₀,…,v_H∈K, having for each construction step t

    |v_(t+1),i−F_i(v_t,q_t)|≤ε a(q_t),
    e_i(v_t,q_t)≤ε a(q_t),
    Σ[t<H]a(q_t)≥Q.

K is fixed before BOTH ε and the requested charge Q. Construction
order runs outward by prefixing, so actual play reverses the word.
That reversal is explicit; horizontal response updates are not inserted
as chronological edges. At this stage the annotations are not asserted
to be payoffs of actual tails.

For normal Fin4 games, the checked fixed-box characterization says:
these words at every ε,Q, OR a sure Nash root at the true punishment
vector, suffice for UE. This is the endpoint I intend to produce,
not a new grammar. The full problem is to force the words or the exit.

The geometric proposal uses a trace-level graph rather than a single
root selector. Several Nash roots can coexist, merge, split, or live
in disconnected payoff components. Their witness tags and exact ports
remain in the object. Small roots approaching AllContinue are recorded
with their first-order directions relative to a(q); roots with a(q)
bounded positively remain literal collision cells. A direction chart
is a limit used to design FINITE words, not an asserted raw-time profile.

## 4. Why closing prices really addresses full cap leakage

The exact semantic prefix map for a tail pair (u,b) is

    u'_i=q_iQ_i+(1−q_i)[A_i+χ_i u_i],
    b'_i=max(Q_i,A_i+χ_i b_i),

where A_i is the passive-opponent contribution. If the tail is diagonal
(v,v) and q is Nash at v, this maps to the diagonal (F(v,q),F(v,q)).
There is then no unpriced nonmover response branch. The max operation
has already priced every response after Continue, not just the next row.

Of course an arbitrary annotation v does not supply a diagonal tail.
The global charged-word compiler is the noncircular part: long compatible
bounded words, with errors proportional to absorption, permit charged
closing and actual punishment completion. It is not enough to invoke
the separately checked finite jump–flow closure of an ALREADY supplied
UE tail; that would assume the equilibrium we want to produce.

The intuitive cap ledger is as follows. At each cut a finite pure
deadline compares Quit-now with the actual declared continuation.
All comparisons are simultaneously bounded by the root inequalities.
When the tail is replaced by its actual compiler output, the residual
is weighted by the appropriate player-DELETED survival, not merely
joint survival. A two-sure root screens every deleted continuation.
A sole-sure root must use that owner's true punishment value; its
off-path continuation cannot be replaced by zero just because prescribed
joint survival is zero. If only one owner remains persistent, the
normality/punishment machinery handles its exceptional deleted tail.

A slow singleton arc is refined only when its owner remains indifferent
and outsiders have the required continuation floor along that arc.
The finite-mesh theorem then controls every outsider deadline, with
collision error proportional to the mesh hazard. A jump is executed
with its actual product coin and actual continuation port. We do not
serially split a macroscopic collision and pretend its rewards survive.
Signed below-singleton payoffs are allowed at other graph points;
the whole diagram is not confined to a positive singleton-flow region.

At the reviewed NP table, naive repetition fails because R_i/(1−h_i)
can exceed the old B_i. A closed continuation-price circuit would instead
solve for ALL relevant phase prices together, including that Never
branch. If the required price rises, the root/phase choices must change
before repetition. The source word is not held fixed. Some rate or
phase can become macroscopic, an observer can activate, or a flow can
switch to a joint jump. A genuine construction must output D≤4ε<δ
on this SAME table; raising another cap and naming it a new price does
not count as success.

This is why the proposal is global. It tries to find one mutually
compatible diagram, not prove that every local debtor reset is good.
The common-debt excursion barrier is allowed: the construction can
leave the old minimum family completely.

## 5. The three unproved mathematical bridges

### B1. An essential index for witnessed continuation diagrams

Proposed bridge: build an absorption-sensitive relative index of the
FULL decorated Nash graph and its small-root direction charts, with
the actual punishment/sure-root exits attached. For four normal players
with nonnegative own rewards and at least one positive own reward,
this essential index is nonzero.

Why this might be true: finite-game Nash degree counts a whole equilibrium
correspondence even when no continuous root selector exists. Known pair
and triple producers already use this distinction to select a good root
despite bad roots elsewhere. Product-root jumps are the actual extra
cells that singleton-only pictures discard. A complete graph retains
those cells and their continuation parameters, rather than requiring a
convex equilibrium-payoff set.

What is NOT proved: the ordinary +1 Nash degree is not automatically
an absorption-sensitive index after zero-charge AllContinue branches
are removed. The relative boundary and its exit labels have to be
constructed, and the normalization shown for the literal game graph.
This cannot be obtained by declaring a correspondence contractible,
by taking its convex hull, or by treating all branches as useful.

### B2. Strategic completion of reentrant boundary contributions

Proposed bridge: an index-carrying boundary component either has a
genuine ambient punishment-priced absorbing exit, or its index is
transported through actual joint-root/continuation cells rather than
being lost at a quiet-child or reentrant corner. The transport retains
the endpoints needed for compatible finite words.

The important mechanism is observer completion. A proper-child
equilibrium is not automatically a full equilibrium. If the fourth
player can profitably join, that joining inequality becomes an active
constraint in the next ambient root cell. If the child members then
want to leave, those leave constraints change the subsequent continuation
prices. One does not discard the outsider or require an immediate
total-debt decrease. The new cell simultaneously prices all four.

Why this might be true specifically in Fin4: every proper active
coalition has at most three members, whose intrinsic equilibrium
problem is solved. The remaining strategic obstruction is at most one
external observer for a triple, or two observers for a pair; they stay
in the ambient graph until safe. The familiar cyclic and two-joint-phase
constructions look like explicit local instances of this closure.
At four active owners there is no unrecorded fifth observer: all debt
leakage has to be represented inside the same four-label continuation
diagram. This is a motivation, NOT a pigeonhole proof or a rank on
support size. Owners can leave and re-enter indefinitely.

The exact topological warning is crucial. In the slab union
{x:min_i x_i≤0}, a three-active reentrant corner can have local relative
Euler contribution +1 even though every individual slab has a strict
descent direction. A four-active corner has a different contribution.
The generic assertion 'no boundary minimum, hence no boundary index'
is false. B2 must compute/cancel/transport these ACTUAL contributions
using the Nash and joining equations. It must not set them to zero.

This is the central unproved bridge, and the most likely place for the
path to fail. At present I do not know whether actual arbitrary signed
four-player root graphs enforce the proposed observer completion.
Neither pure-coalition escape nor a local +1 degree suffices.

### B3. Essential index cannot be parked at zero physical charge

Proposed bridge: if no genuine sure-root exit occurs, the continued
essential component supplies finite compatible words with arbitrarily
large absorption charge, at every requested absorption-relative error.
It cannot terminate as an all-Continue self-loop, an unpriced late
test, or an index label at a Zeno endpoint with no actual continuation.

Why this might be true: a normalized small-root direction that carries
the index should integrate to a proper coarse arc; a nonsmall root
already carries absorption. A continuing component then has either
recurrent positive-charge pieces or a new boundary piece to which its
index passes. A source-matched repeated piece closes, whereas a new
piece is handled by B2. A true punishment exit handles a unique sure
supplier instead of losing its deleted survival.

The necessary quantitative content is substantial. Errors must be
small compared with CHARGE, not just tend to zero absolutely. Local
progress may shrink; a finite owner set does not bound ordinal clock
depth or rule out nested accumulation. Therefore I would prove B3
by contradiction from a bounded-capacity rank, not by pretending that
one arbitrary selected infinite path is proper. Its output is a FINITE
word for each ε,Q; no universal period, exact finite-menu Nash, or
attained integer-clock minimum is needed.

The existing counterexample-to-UE polynomial theorem supplies that
contradiction target precisely. If no UE exists, there is a positive
rational tolerance and a bounded rational polynomial P such that

    P(F(v,q))+a(q)≤P(v)

on every exact boxed root, and the corresponding strict charge drift
on every allowed robust edge. Along any compatible construction word
P drops by at least its total charge. Large charge is impossible in
a compact box. B1–B3 are meant to show that a FULL GAME graph cannot
have all its essential index absorbed by such a bounded acyclic rank.
This does not require excluding only additive, quadratic, multi-affine,
or convex P; those exclusions are already known and do not close the
problem. A surviving P can have genuinely nonlinear mixed curvature.

## 6. The complete proposed route from arbitrary rewards to UE

1. Start with any signed four-player table. Use exact existing positive
   branches when available, but do not assume their union is exhaustive.
   For the contradiction route assume this table has no UE. Checked
   low-cardinality/normal-core results then give its all-player normality
   and true punishment bounds. Apply the actual single-pivot semantic
   normalization, not an informal inverse row-affine invariance. The
   resulting table has own rewards (1,0,0,0), all other rows signed.
   Scale positively to a bounded table if desired.
2. Fix this ONE resulting table. Build its full decorated continuation
   graph. If it has a sure root at the TRUE punishment vector, the
   checked consumer gives UE and the actual normalization adapter
   transports that conclusion back to the original table.
3. Otherwise apply B1 and B2 to continue the essential index through
   every intrinsic child, unsafe outsider, macroscopic collision,
   singleton flow and reentrant stratum. No selected child is silently
   certified safe. No minimum payoff or cap is used as a supplied
   Nash continuation.
4. Apply B3. For every ε>0 and charge request Q≥0 obtain the finite
   absorption-weighted Bellman/Nash word from Section3, in one fixed
   box. Equivalently, the bounded strict polynomial rank forced by
   no UE is contradicted by those actual graph words.
5. Use the existing weighted-packet repair, charged closing and actual
   profile compiler. For every desired terminal Nash accuracy this
   produces one literal independent behavioral profile controlling
   ALL finite deadlines and Never. It is not enough to report small
   stage regrets or a finitely additive Nash boundary packet.
6. Select a convergent subsequence of prescribed payoffs as terminal
   error tends to zero, so the same subsequence has (U,B)→(v,v).
   The checked diagonal-carrier/terminal selection endpoint gives one
   FIXED UE payoff. Transport through the actual normalization adapter.
   This contradicts the initial no-UE hypothesis and proves UE for
   every four-player table, IF B1–B3 are established.

This is an all-branch route. The current paid nonsure source is its
hard adversarial instance, not an additional branch assumed solved.
Applying the same proposed graph principle directly at that fresh
normal positive-own table would yield D<δ there and contradict its
global floor. None of the single-pivot table's minima, MAX witnesses,
absorbing minima, or diagram tags are carried into the NP table.

## 7. Four decisive tests, and what would kill the path

### Test1: disconnected correct targets versus a false symmetric limit

Use the COMPLETE solved table r_i({i})=C≥1, r_i(S)=C−1 for nonsingleton
participants, and r_i(S)=C+1 for passive recipients. Its ordinary
UE-payoff set is exactly four singleton vectors, while exhaustive
full-support finite-menu equilibria can have a refined finitely additive
limit with false payoff C·1. The omitted moving deadline retains debt
4C/(C+1). This was proved exactly in FA1–FA7 of the owned notebook.

The proposed diagram must retain four distinct absorbing exits; it
must NOT convexify them or follow only the symmetric finite-menu
branch. Here an exact singleton root is Nash against a continuation
whose owner coordinate is at most C; passive outsiders are already
protected. This is a simple positive check for index-carried SELECTION
rather than preservation of all equilibrium branches.

### Test2: inert finite-menu roots, but a successful growing clock

Use the complete cyclic RZ table in the owned notebook. Its zero-own
singleton matrix is R₀/StandardQ/degree1 with a positive simplex image;
every pure absorbing coalition has a strict escape. Yet every exact
finite-calendar Nash profile is AllNever. Proper repeated four-owner
blocks have fixed target and full debts at most98ρ per owner, with
ρ→0 under refinement and deleted-opponent contraction σ³ per period.

The diagram has to keep the normalized singleton-flow branch and
approximate finite execution. It must not demand an exact finite-menu
Nash endpoint, a bounded exact period, or a root at continuation0.
Failure to recover this existing execution kills B3's proposed treatment
of neutral/late boundary points before any general theorem is attempted.

### Test3: a bad positive-index root and a genuinely reentrant corner

Use BOTH an opposite-join-sign two-owner root module and NOETHER's
three-active reentrant local pair. The complete module is

| coalition | owner i payoff | owner j payoff |
| --- | ---: | ---: |
| {i} | 1 | 3 |
| {j} | 1 | 1 |
| {i,j} | 2 | 2 |

At continuation v=(2,0), the two gaps are −1+2q_j and1−2q_i.
The UNIQUE Nash root is q_i=q_j=1/2. Both endpoint values and both
successor payoffs are3/2, above the two own singletons1, although the
source's j-coordinate lies below its singleton. No pure root is Nash.
The nondegenerate mixed equilibrium has local index +1; the product
of the two cross-gap slopes is negative. This is a local two-owner
module, not a claim of unique Nash over an unlisted four-player table.
The module itself has an exact full singleton Nash with payoffs(1,3).
Thus its bad root tests selection, not existence.

For the reentrant test, use D₃×ℝ near0 with
ψ(x,t)=−x₀−x₁−x₂+t² and D₃={x:min_k x_k≤0}. Every active slab
has a descending segment in some other active coordinate, but the
local descending link is S¹ and the sublevel pair contributes +1.
There is no constrained boundary minimum there. These exact tests
forbid claiming that all bad roots have negative index or that all
boundary contributions disappear.

The first substantive calculation I would request is the local
continuation INDEX ACCOUNT near a three-active own-threshold stratum,
with the fourth owner's ALL joining/withdrawal payoffs retained.
Show an actual ambient Nash branch transporting the positive index,
or a safe punishment-priced terminal exit. A realizable four-player
counterexample to that local strategic account would kill B2 as
stated and change the mechanism. A generic star-shaped topological
counterexample alone does not answer the game-specific question.

### Test4: the reviewed nonsure fully-paid source, with its full renewal cap

At ONE NP table retain δ,g,d*, the positive Never masses, and the
whole active cap family. The diagram must allow asynchronous rates,
different phase lengths, and literal macroscopic joint roots. It must
price R_i/(1−h_i), not merely B_i, when closing a proposed period.

Demand an actual word/profiles with D<δ. A best reply whose nonmover
debts rise, a new minimum at a DIFFERENT table, a repetition of the
old word, or a condition 'assume the seam is admissible' fails this
test. The proposed global index theorem is valuable only if it forces
a NEW compatible circuit on that fixed table despite those obstructions.

## 8. Known no-gos this path is designed to avoid

The choice of a witnessed global graph is deliberate:

- A root Nash at prescribed continuation U need not control full cap B.
  Closing annotated words and actual tails is indispensable.
- Positive-debtor replies cannot remain at the common-debt minimum;
  no minimum-return support rank is invoked.
- Fixed-row tail optimization and alternating row/tail optimization can
  be globally trapped in their chosen blocks. The whole word is selected.
- Stationarity, diagonal hazard acceleration, and uniform common-date
  replicas are not complete. Rates and phases can be asymmetric.
- Quiet-child NE alone is not an ambient UE; every outsider remains
  in the graph until its full joining clock is safe.
- Joint survival does not control deleted survival. A unique sure owner
  still exposes a punishment continuation under its own deviation.
- Finite-menu NE, fixed-test convergence and finitely additive refinement
  do not control moving complete responses. The full packet compiler is
  the semantic endpoint, not a weak clock limit.
- The actual UE-payoff set and jump images can be nonconvex. No convexified
  payoff selection or public lottery between components is used.
- Horizontal replacements, table changes and compact-source regeneration
  are not chronological edges. Only matched root words are executed.
- Absolute endpoint errors do not imply error/charge control. The required
  Bellman and Nash tolerances are explicitly absorption-relative.
- A compact carrier minimum is not necessarily an attained raw profile,
  and an absorbing minimum is not an original full minimum. Neither
  inference appears in the proposed graph construction.
- Four owner labels do not bound clock depth or guarantee that a selected
  Zeno path is executable. The goal is finite ε,Q words, not that shortcut.

## 9. Evidence map and the honest next step

The bounded reading for this bird's-eye assignment used `FRONTIER.md`,
`GOAL.md`, the architecture notes on sufficient state, controller/tester,
semantic barriers, chronological occupation, recurrence obstruction and
neutral chronology, and the reviewed fully-paid nonsure source. Existing
raw classes were read as sufficient classes, not a global census. The
global-route/one-jump APS notes and the owned FA/JF/RZ/HN/HF tests supplied
the exact failure boundaries above. NOETHER's TG7 local-index calculation
was read as a falsifier, not as an index consumer.

The concrete tracked interfaces inspected in their source files were:

- `quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot`
  (`UniformEquilibrium/Quitting/Projective/FixedBoxForwardCharacterization.lean`);
- `HasAbsorptionWeightedFiniteForwardPackets` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
  (`UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketProducer.lean`);
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`);
- `IsQuittingFullExactRootPotential` and
  `isQuittingFullExactRootPotential_of_robustPotential`
  (`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`);
- `CompatibleFiniteJumpFlowWord.execute_error_and_debt_le`
  (`UniformEquilibrium/Quitting/EssentialAPS/FiniteJumpFlowCompiler.lean`),
  with its SUPPLIED compatible word and tail hypotheses kept explicit;
- `isUniformEquilibriumPayoff_singletonArc_before_rootSuccessor`
  (`UniformEquilibrium/Quitting/EssentialAPS/JumpFlowClosure.lean`),
  which requires an already supplied uniform-payoff tail;
- `isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier`
  (`UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`);
- `exists_recipientScale_all_minimum_debts_eq`
  (`UniformEquilibrium/Quitting/Terminal/RecipientScaledTerminalSemantics.lean`)
  and `exists_recipientRigid_signAdaptiveContact_source_of_not_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticRecipientRigidContactSource.lean`).

No Lean implementation, build, Git action, or export is part of this
intuition-level investigation. The recent raw-Simon rank composition
may offer another precise version of the same acyclic obstruction; it
is not needed as an unreviewed source premise here. Its nonconvex index
gap remains a genuine gap, not a missing name for an existing theorem.

My current belief is that a proof is more likely to need this global
selection/closing mechanism than a universal one-response gain lemma.
But the confidence is conditional on the strategic reentrant-index
account, not on generic topology. The next decisive task is Test3's
actual four-player local account, INCLUDING its ambient continuation
ports and positive-charge orientation. If that account fails, this
proof picture should be changed, not repaired by assuming away the
unsafe observer or convexifying the continuation family.
