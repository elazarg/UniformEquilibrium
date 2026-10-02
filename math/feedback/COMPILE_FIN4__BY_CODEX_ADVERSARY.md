# Adversarial mathematical review of `COMPILE_FIN4.md`

Reviewer: Codex Adversary

## Verdict

Do **not** export the note as a whole in its present form.

There is one rigorous, conjecture-facing core: Proposition 2, after replacing
the undefined phrase “source-faithful behavioral limit” by an exact statement
about the induced stopping laws in total variation.  It applies directly to
the fixed-terminal realization used by the current Fin4 maximal-prefix stall,
and it has a useful quantitative strengthening: for every member of the
retained coalition, the stopping-law sequence remains at a fixed positive
total-variation distance from every candidate actual limiting law.

Proposition 1 is mathematically correct after restricting the parameter to a
probability interval and specifying the topology, but it is a zero-global-
minimum example and substantially overlaps the already checked zero-minimum
maximal-ray regressions.  Its genuinely stronger feature is only a positive
**local** debt floor along the displayed curve.  That is not presently a
strict conjecture-facing change by itself.

Proposition 3 correctly shows that the four coordinates of
`QuittingMarkedPairDecoration` do not control tightness of a *chosen lifting*
by actual rows.  It does **not** prove nonactualizability of the decoration:
the note itself gives an exact actual realization.  More seriously, the
example has whole debt zero, whereas the normalized passport used in the Fin4
minimum-return route has strictly positive whole debt.  Consequently the
example does not instantiate the actual normalized-passport domain and cannot
support the claimed necessity of adding `TightPort` fields to that adapter.

The relaxed-root argument is a valid local comparison-transport lemma.  It is
not a summable decoder or uniform-escape consumer until its one-step semantic,
cap, law, ancestry, and accumulated-error estimates are proved.

This is an ordinary-mathematics review.  Nothing in this review has been
checked by Lean.

## Claim reviewed

The note proposes a seven-instruction executable schema and asserts three
obstructions:

1. nonclosedness of global absorption-maximal exact root selection;
2. stopping-law escape on every positive-debt infinite exact left-prefix
   chain retaining a positive finite atom; and
3. failure of normalized decorations with positive mass and gain to actualize
   without stopping-law tightness.

It also proposes a tight-port realization lemma and a relaxed-root
comparison-transport repair.  I checked each item separately, including its
purported attachment to the current Fin4 source.

## 1. Proposition 1: correct mathematics, repaired statement required

### Exact calculation

Take the displayed table

\[
r_0(S)=\mathbf 1_{\{1\in S,\ 0\notin S\}},
\qquad
r_j(S)=-\mathbf 1_{\{j\in S\}}\quad(j=1,2,3),
\]

and restrict the parameter to \(t\in[0,1]\).  Let player 1 stop at date zero
with probability \(t\), player 3 stop there with probability \(1/2\), and
players 0 and 2 Never stop.  Then

\[
U(\tau_t)=(t,-t,0,-1/2),
\qquad
B(\tau_t)=(t,0,0,0),
\]

so

\[
D(\tau_t)=t+1/2.
\]

The cap calculations cover unrestricted behavioral deviations.  Player 0
gets \(t\) by Never or by waiting past date zero, and quitting at date zero
suppresses the only positive outcome.  Each of players 1, 2, and 3 gets zero
by Never, while any event in which that player quits pays at most zero.

At continuation cap \((t,0,0,0)\), players 1, 2, and 3 strictly prefer
Continue in every root: Continue pays zero and Quit pays \(-1\).  Once they
continue surely, player 0 compares Continue payoff \(t\) with Quit payoff
zero.  Therefore all-Continue is the unique exact root for \(t>0\).  At
\(t=0\), player 0 is indifferent, every mixture of its two actions is exact,
and absorption is maximized uniquely by its sure-Quit root.  Thus the graph of
global absorption-maximal exact roots is not closed.

### Necessary corrections

- “For every \(t>0\)” is false as written because \(t\) is used as a
  probability.  State \(0<t\le1\), or use a sequence
  \(t_n\downarrow0\) in that interval.
- A `BehaviorProfile` is not itself given the unnamed total-variation
  topology used in the prose.  State that each player's induced stopping law
  converges in total variation; equivalently, state convergence of the finite
  tuple of stopping laws in the strategic \(\ell^1\) metric.  For player 1
  the distance to the \(t=0\) law is exactly \(t\); all other marginal laws
  are fixed.
- The conclusion “no continuous selector exists” is correct only for a
  selector whose value is required to be a *globally absorption-maximal exact
  root* at every displayed cap.

### Novelty boundary

The current checked Research surface already has actual zero-minimum Fin4
maximal rays whose canonical maximal roots converge to all-Continue while a
separate positive-absorption exact root exists at the limiting cap.  This is
recorded by `Regression.canonical_root`,
`Regression.root_quit_tendsto_zero`, `Regression.limitRoot_exactNash`, and
`Regression.limitRoot_positive` in
`Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean`.  Those facts
already witness the same nonclosed maximal-root mechanism.

The displayed example here is simpler and keeps \(D(\tau_t)\ge1/2\) along
its chosen curve, but its table still has global minimum zero (all-Never has
zero debt).  The review therefore rejects “new global maximal-root
nonclosedness” as an export-level novelty claim unless the packet explicitly
distinguishes and justifies the value of the positive *local* floor.

## 2. Proposition 2: valid core and quantitative strengthening

Let

\[
\sigma_0=\tau,
\qquad
\sigma_{n+1}=x_n\star\sigma_n,
\qquad
c_n=\Pr_{x_n}(\text{all Continue}),
\qquad
C_n=\prod_{k<n}c_k.
\]

Assume every \(x_n\) is exact cap--Nash against \(\sigma_n\),
\(D(\sigma_n)\ge D_*>0\), and \(\tau\) has terminal coalition \(S\) at
date \(s\) with mass \(m>0\).

The exact prefix identity gives

\[
D(\sigma_n)=C_nD_0,
\qquad D_0=D(\tau),
\]

and hence

\[
C_n\ge q:=D_*/D_0>0.
\]

The retained event is at date \(n+s\) in \(\sigma_n\), with mass
\(C_nm\ge qm\).  For every \(i\in S\), this event is contained in
\(\{T_i=n+s\}\).  Thus for every finite cutoff \(T\), some row has at least
\(qm\) finite stopping mass after \(T\).  This proves failure of a common
finite-tail envelope.

Since \(C_n\) is decreasing and bounded below, it converges to a positive
limit and

\[
c_n=C_{n+1}/C_n\longrightarrow1.
\]

Put \(a_n=1-c_n\).  In \(\sigma_n\), the root at a fixed absolute date
\(t<n\) is \(x_{n-1-t}\).  A player's Quit probability at that root is at
most its total absorption probability \(a_{n-1-t}\), so

\[
\Pr_{\sigma_n}(T_i=t)\le a_{n-1-t}\longrightarrow0.
\]

If \(p_{i,k}\) is player \(i\)'s Continue probability in \(x_k\), then

\[
P_{i,n}:=\prod_{k<n}p_{i,k}\ge C_n\ge q.
\]

The products converge to some \(p_i\ge q\), and the Never coordinate is

\[
\Pr_{\sigma_n}(T_i=\infty)
=P_{i,n}\Pr_\tau(T_i=\infty)
\longrightarrow
p_i\Pr_\tau(T_i=\infty).
\]

Because the retained coalition event implies \(T_i=s\),
\(\Pr_\tau(T_i=\infty)\le1-m\).  The coordinatewise finite-plus-Never limit
therefore has total mass at most

\[
p_i(1-m)\le1-qm.
\]

This proves all four elementary assertions once the final one is phrased as
“there is no limiting probability law preserving every finite coordinate and
the Never coordinate,” or, more strongly, as a total-variation statement.

### Stronger total-variation conclusion

Let \(\lambda_i^n\) be the stopping law of player \(i\) in \(\sigma_n\), and
let

\[
L_i=p_i\Pr_\tau(T_i=\infty),
\qquad
h_i=1-L_i.
\]

For every actual probability law \(\mu_i\) on
\(\mathbb N\cup\{\infty\}\), test total variation on

\[
A_T=\{0,\ldots,T\}\cup\{\infty\}.
\]

For fixed \(T\), \(\lambda_i^n(A_T)\to L_i\), while
\(\mu_i(A_T)\uparrow1\).  Hence

\[
\liminf_n d_{\rm TV}(\lambda_i^n,\mu_i)
\ge 1-L_i=h_i\ge qm.
\]

Thus every retained-atom marginal is separated from **every** candidate
actual stopping law by the fixed TV floor \(qm\).  This is the cleanest
exportable formulation.  If the project uses \(\ell^1\) rather than the
half-\(\ell^1\) convention for TV, the displayed floor becomes \(2qm\).

### Exact Fin4 attachment

This theorem really does attach to the strict maximal-prefix stall.  The
fixed terminal is `packet.rayBaseProfile 0`, not the varying moving family.
The required facts are supplied by:

- `quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq` and
  `quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq` in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
- `quittingMaximalCapSemanticPrefixSurvival_tendsto_limit_div` and
  `quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add` in
  `Research/Quitting/MaximalCapSemanticPrefixReturn.lean` and its imported
  orbit interface;
- `FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayBaseProfile_stageMass_eq_one`
  and the fixed-terminal `MaximalPrefixRayStall.retainedLaw` construction in
  `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`.

For this attachment, \(m=1\) at the fixed pure pair and
\(q=D_*/D_0\).  Every player in that pair has TV separation at least \(q\)
from every actual candidate law.  The existing retained-law cluster is only
a time-forgetting semantic/outcome-law carrier point, so this result does not
contradict its construction.  It proves that the cluster may not be installed
as the ancestry-preserving strategic-TV limit of the displayed profiles.

This narrows the exact operation requested in
`questions/FIN4_RECURRENT_COMPONENT_CONSUMER_OR_MODEL.md`.  It does not
consume the strict ray, rule out a summable decoder, or imply a uniform payoff.

## 3. Proposition 3: exact example, invalid advertised consequence

### What the example proves

For the displayed table, if \(\sigma_n\) has player 0 quit surely at date
\(n\), then

\[
U(\sigma_n)=B(\sigma_n)=(0,1,0,0).
\]

Its time-forgetting terminal law is the point mass at \(\{0\}\), its
postmark tail is all-Never with zero semantic pair and Never outcome law, its
marked mass is one, and player 0's marked-root defect is zero.  If
\(\widehat\sigma_n\) instead has player 2 quit surely at date \(n\), then
the gain-mover coordinate satisfies

\[
U_1(\sigma_n)-U_1(\widehat\sigma_n)=1.
\]

These are exactly the fields of `QuittingMarkedPairDecoration`: the
comparison profile contributes only the scalar gain, not a comparison-law
coordinate.  Thus `baseDecoration n` is constant.

Player 0's induced stopping law is \(\delta_n\).  Every fixed finite
coordinate and the Never coordinate converge to zero, and for every cutoff
\(T\),

\[
\sup_n\Pr_{\delta_n}(T_0>T)=1.
\]

No strict subsequence is tight.  Therefore the decoration projection does not
control tightness of an arbitrarily chosen realizing sequence.

### Why the claimed obstruction does not follow

The decoration point is actually attained: replace date \(n\) by date zero
in both profiles.  That replacement preserves the whole semantic/outcome-law
point, postmark semantic/outcome-law point, marked mass, actual gain, and
marked-owner defect.  It even gives a constant tight realizing family.

Accordingly, the example does **not** prove any of the following:

- that the compact decoration point is behaviorally nonattained;
- that every compiler from that decoration must lose ancestry;
- that no executable successor can be selected from the decoration; or
- that a tightness passport is necessary, rather than merely sufficient, for
  actualization.

The phrase “source-faithful” is doing all the work, but no ancestry relation
is defined which excludes the date-zero realization.  The current carrier
actualizer explicitly does not require its origin ranks to be cofinal.  Thus
failure of cofinal convergence of this particular lift is not yet a
counterexample to the actual adapter class.

There is a second mismatch.  Here the whole debt is zero because
\(U(\sigma_n)=B(\sigma_n)\).  By contrast,
`QuittingMarkedPairMinimumTailSelection.limit_wholeDebt_pos` in
`Research/Quitting/FixedPairMinimumTailNormalizedReturn.lean` and the
`wholeDebt_pos` field of `QuittingNormalizedPassport` in
`Research/Quitting/NormalizedPassportMinimizer.lean` put the Fin4 normalized
passport in a strictly positive whole-debt domain.  The example therefore
does not test that domain.

### Repair needed for an accepted negative answer

Retitle this as a nonproperness result for the decoration projection, and
remove the claim that the current actualizer “needs” `TightPort` fields.
To obtain the stronger advertised result, define an exact cofinal ancestry
relation and prove that **every** lift respecting it inherits the escaping
clock.  Alternatively, produce two source-attached families with identical
decorations but incompatible legal successors, as invited by the recurrent-
component question.  A closer local regression should also have positive
whole debt; for example an additional player with a profitable own-Quit
option makes the displayed rows have fixed positive local debt, although the
global minimum of that modified table remains zero.

No example satisfying the full positive-global-minimum Fin4 hypotheses is
currently available; producing one would itself be counterexample-level
progress.

## 4. Tight-port realization lemma

The lemma is correct under a fixed TV convention.  Coordinate convergence,
separate Never convergence, and a common finite-date tail envelope imply that
the candidate coordinates sum to one and that the laws converge in total
variation.  The hazard quotient realizes every resulting law exactly.
Product coupling and contraction through the labelled first-stopping map then
give uniform convergence under every one-coordinate replacement, hence
convergence of prescribed payoffs and unrestricted behavioral caps.

Two scope corrections are needed.

1. The lemma is a sufficient actualization criterion, not a necessary one.
   A nontight chosen lift may project to a point with another tight actual
   lift, as Proposition 3 itself demonstrates.
2. The result already appears in substance in
   `exports/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md` and in
   the stopping-law realization/total-variation interfaces.  It should be
   cited rather than presented as new export content.

The relevant checked interfaces include
`quittingBehaviorStoppingLaws_update`,
`quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
`quittingBehaviorDeviationPayoffCap_eq_pureTime` in
`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`, together
with `quittingStoppingLawBehaviorStrategy` and
`quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`.

## 5. Relaxed-root repair

Let \(g(b,x)\) be the maximum coordinate Nash defect and \(a(x)\) the
absorption mass.  Both are continuous on the finite root simplex, and the
displayed conservative bound

\[
|g(b,x)-g(b',x)|\le2\lVert b-b'\rVert_\infty
\]

is sufficient.  If \(b_n\to b\), \(\delta_n=\lVert b_n-b\rVert_\infty\),
and \(x_n\) maximizes \(a\) on

\[
N_n=\{x:g(b_n,x)\le2\delta_n\},
\]

then \(N_n\) is nonempty and compact.  Every cluster point \(x\) of
\(x_n\) is exact at \(b\).  For every exact root \(y\) at \(b\), the
Lipschitz bound gives \(y\in N_n\), so

\[
a(y)\le a(x_n)\longrightarrow a(x).
\]

Thus \(x\) is absorption-maximal among exact roots at \(b\).  This argument
is valid.

What is not proved is the promotion from this one-sequence lemma to the
`SummableMacro` claimed by the note.  A usable decoder still needs:

- exact approximate-prefix payoff, cap, debt, terminal-law, and deleted-law
  error inequalities;
- one common triangular code and fixed-column convergence for all persistent
  ports, not a new subsequence for each occurrence;
- a uniform summable tail estimate and closed ancestry; and
- an approximate same-tail dispatch plus a terminal or renewable-rank
  consumer.

The note acknowledges most of these omissions.  Consequently §5 should be
labelled a surviving local lemma, not “the valid replacement” as though the
uniform-escape edge had been compiled.

## 6. Other overclaims in the architecture sections

- The seven instruction names are a design sketch, not a proved “sufficient
  finite program schema.”  No trace syntax, semantics, projective-limit
  theorem, or induction compiling arbitrary programs to a behavioral
  construction is given.  The already exported executable grammar is the
  proper source for such a theorem.
- The address budget assumes at most \(2^d\) addresses at depth \(d\) without
  defining a binary encoding of the finite branch alphabet.  The numerical
  bound is conservative once a binary encoding is fixed, but the encoding is
  part of the missing program semantics.
- “No suffix with reach tending to zero may be installed” is too strong as a
  universal mathematical statement.  Vanishing reach means that convergence
  of the whole profiles alone does not determine the conditional suffix.  A
  constant suffix family, or a separately convergent and recorded suffix
  family, can still have a legitimate limit.
- The regeneration discussion is accurate for the older three-role equality
  regeneration, but it must not be stated as the status of all current Fin4
  regeneration.  The canonical-pair support-handoff branch now has the
  source-attached rank and well-founded transition recorded by
  `canonicalPairRenewableTransitionRel_wellFounded`, `descentCount_le_three`,
  and `exists_renewalTerminalExit_sameResidual` in
  `Research/Quitting/FinFourProducerAtlas/CanonicalPairRenewableSourceRank.lean`
  and `CanonicalPairMinimumEndpointRenewal.lean`.  Its three terminal exits
  and backward strategic consumers remain open, so it does not complete the
  requested program, but the note's source table must distinguish this branch
  from unranked three-role regeneration.

## Source declarations and files inspected

- `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`;
- `VanishingDebtAtomChronologicalConsumer` and
  `PaidFirstDisagreementAdmissibleReturnConsumer` in
  `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`;
- `quittingTerminalSemanticCarrier` and
  `exists_terminalProfile_sequence_tendsto_semanticPair` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingRootCoordinateNashDefect`,
  `isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero`, and the
  continuity declarations in `UniformEquilibrium/Quitting/Root/NashDefect.lean`
  and `NashDefectContinuity.lean`;
- `quittingBehaviorStoppingLaws_update`,
  `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime` in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`;
- the stopping-law realization interface in
  `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`;
- the discrete tightness/TV equivalence in
  `MathUE/ProbabilityMassFunction/DiscreteTightness.lean`;
- `quittingMaximalCapSemanticPrefixOrbit`, its literal profile realization,
  survival, debt-scaling, and stage-mass declarations in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean` and
  `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`;
- the fixed-terminal strict-stall adapter in
  `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`;
- `QuittingMarkedPairDecoration`, `baseDecoration`, and
  `descendant_postMarkSpine_eq` in
  `Research/Quitting/NormalizedPassportPrefixOrbit.lean`;
- `QuittingMarkedPairMinimumTailSelection.limit_wholeDebt_pos` in
  `Research/Quitting/FixedPairMinimumTailNormalizedReturn.lean`;
- `nonempty_quittingMarkedPairCarrierActualizer` and
  `toDecoratedFamily_baseDecoration_tendsto` in
  `Research/Quitting/NormalizedPassportCarrierActualizer.lean`;
- the zero-minimum maximal-ray regression surface in
  `Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean`;
- the renewable canonical-pair source-rank declarations in
  `Research/Quitting/FinFourProducerAtlas/CanonicalPairRenewableSourceRank.lean`
  and `CanonicalPairMinimumEndpointRenewal.lean`;
- the exact current branch descriptions in `docs/FRONTIER.md` and
  `docs/TOOLKIT.md`; and
- the gate and prior grammar in `exports/README.md` and
  `exports/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md`.

No literature theorem is invoked by the note, so no paper-source adapter was
needed for this review.

## Export recommendation

The complete note fails the mandatory gate: its program schema is not a
theorem, Proposition 3 does not prove its advertised adapter impossibility,
the source audit omits existing maximal-root and renewable-rank results, and
the tight-port material duplicates a prior export.

A revised packet containing only the following could pass a new review:

1. the exact strategic-TV prefix-escape theorem, including the lower bound
   \(\liminf d_{\rm TV}\ge qm\);
2. its explicit specialization to the fixed-terminal
   `MaximalPrefixRayStall` source, with the precise named Fin4 obligation it
   narrows;
3. Proposition 1 only as a boundary regression, with \(t\in[0,1]\), the
   zero-global-minimum fence, and comparison to the existing maximal-ray
   regressions; and
4. the relaxed-root result only as a still-unconsumed possible repair.

Proposition 3 may remain in an internal note as a projection-nonproperness
example.  It should not be used to claim that tightness is a necessary field
of the current normalized actualizer without the stronger ancestry theorem
described above.

## Addendum: focused review of `POSITIVE_MINIMUM_EXACT_PREFIX_CLOCK_ESCAPE.md`

### Gate verdict

**FAIL as written, but PASS after the source-attachment edits below.**  I
found no counterexample to Theorem A or Theorem B.  The failure is presently
one of self-contained notation and exact source correspondence, not of the
clock-escape argument.

The unit-separation claim in Theorem B is exact.  If \(\lambda_n\) is the
pair member's stopping law, then for every fixed \(T\),

\[
  \lambda_n(\{0,\ldots,T\}\cup\{\infty\})\longrightarrow0.
\]

For any fixed law \(\nu\), total variation tested on this event gives

\[
  \liminf_n d_{\rm TV}(\lambda_n,\nu)
  \ge \nu(\{0,\ldots,T\}\cup\{\infty\}).
\]

Letting \(T\to\infty\) gives the lower bound one; since the stated
half-\(\ell^1\) normalization is at most one, the distances actually converge
to one.  Hence no cofinal subsequence can converge in total variation.

The exact varying-tail Fin4 adapter is also mathematically valid, but it must
be written explicitly as

\[
  \tau_n:=\texttt{packet.rayBaseProfile n},\qquad
  Z_n:=\texttt{packet.rayFamily.rayProfiles n}.
\]

Here the outer word is
`quittingMaximalCapSemanticPrefixRootStack`, its survival is
`quittingMaximalCapSemanticPrefixSurvival`, and its chronological root at
fixed date \(t<n\) is the root with orbit index \(n-1-t\).  The declarations
`QuittingCommonSemanticMarkedBaseFamily.rayProfiles`,
`quittingMaximalCapSemanticPrefixRootStack_succ`,
`quittingMaximalCapSemanticPrefixProfile_eq_literalRootStack`,
`rayProfiles_wholeDebt_eq`, `packet.rayProfiles_wholeDebt_tendsto`,
`packet.minimumDebt_le_rayLimit`, and
`packet.rayProfiles_stageMass_eq_survival` establish exactly the varying-tail
word, positive survival limit, and shifted pair mass used in the proof.
For each member of `packet.rayTerminal`, the date-zero root of \(\tau_n\) is
the pure quitting root, so its individual Never coordinate is zero.  Thus
Theorem B applies and gives unit, not merely positive, TV escape.

### Mandatory edits

1. Define the corollary's previously free symbol
   \(D_*:=\texttt{quittingTerminalSemanticDebtSum source.point.1}\), set
   \(D_0:=\texttt{quittingTerminalSemanticDebtSum packet.raySource}\), and
   \(L:=\texttt{packet.rayLimit}\).  Then
   `minimumDebt_le_rayLimit` gives \(L\ge D_*>0\) (strict inequality in the
   strict arm), and the displayed ratio is well-defined.
2. Do not cite `packet.rayBaseProfile_neverMass_eq_zero` as the individual
   zero-Never premise of Theorem B.  That declaration concerns the **joint
   terminal-outcome** coordinate `none`; it is weaker than an individual
   marginal statement.  Derive the marginal fact directly from
   `rayBaseProfile`, `quittingPureSetRoot`,
   `quittingSetAction_eq_true_iff`, and the stopping-law definitions, or add
   the proposed checked lemma
   `maximalPrefixRay_pairMember_neverMass_eq_zero`.  The ordinary-mathematics
   derivation is immediate, but the source audit must not conflate the two
   notions.
3. Distinguish the varying family above from
   `MaximalPrefixRayStall.retainedLaw`, whose declared tail is the fixed
   `packet.rayBaseProfile 0`.  The fixed-tail object is covered by Theorem A
   (and, because its pair members also have zero Never mass, enjoys the same
   unit-TV strengthening); it is not the rank-dependent adapter displayed in
   the corollary.
4. For Theorem A's identity on **actual** profiles, add either
   `quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash`
   from `TerminalCapNashEndpointTransport.lean`, or explicitly pair
   `quittingTerminalSemanticPair_rootThenContinuation` with the cited
   semantic debt-scaling theorem.  The currently cited semantic theorem alone
   does not state the actual-profile splice identity.

After these edits, the packet meets the named question's second acceptable
partial-answer criterion: it specifies one operation (the canonical reverse
maximal-root prefix word), one adapter class (raw ancestry-preserving
strategic-TV compactification), proves that adapter impossible, and lists the
remaining finite-stop, summable-decoder, and independently tight-source
options.  It still does not consume the strict component, as the packet
correctly states.

**Final focused verdict: PASS — the four mandatory source-attachment repairs and the unit-total-variation strengthening are correctly applied.**
