# Audit of the executable compact-state proposal

## Verdict

The note contains two sound and useful mathematical results once they are
separated from the informal program architecture.

1. Pointwise convergence of all finite stopping-time atoms and of the Never
   atom, together with eventual uniform tightness of the remaining finite
   tail, gives total-variation convergence to one actual stopping law.  For a
   finite family of source ports this commutes with fixed finite prefixing,
   complete unilateral replacement and positive-reach suffixing.  It also
   gives uniform convergence of every pure-time/Never response menu and hence
   of the unrestricted behavioral caps.
2. The diffuse-clock/tester table gives a coherent split-clock boundary point
   with positive late-finite mass that has no actual realization.  The
   late-mass capacity inequality gives a fixed (1/2) failure for the stated
   summable coordinate budget.

These results answer meaningful parts of
`QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`.  The full “executable
finite-program state theorem” is not yet a theorem at the same level of
precision: the program language, its legal executions, the extension order,
and the two nonactual passport types are descriptions rather than defined
mathematical objects.  It should not be exported as one capstone without
first extracting those definitions and weakening several conclusions below.

## 1. Exact stopping-law layer

The identification of a quitting behavioral strategy with a probability law
on

\[
K=\mathbb N\sqcup\{\infty\}
\]

is correct for the unique live history of a quitting game.  Conditional
hazards reconstruct every such law.  Against fixed independent opponent
laws, an arbitrary behavioral replacement is a probability mixture of the
pure dates and Never.  Therefore

\[
B_i(\mu)=\sup_{t\in K}U_i(\delta_t,\mu_{-i})
\]

is the unrestricted behavioral cap.

The distinction between the late-finite limit and Never is also correct.  On

\[
\widehat K=(\mathbb N\cup\{\omega\})\sqcup\{\infty\},
\]

the finite response menu has the stated continuous extension at \(\omega\),
whereas \(\infty\) is isolated.  The maximum over \(\widehat K\) equals the
supremum over the actual actions in \(K\), even if the maximum occurs only at
\(\omega\).

This split compactification does not by itself determine the joint terminal
coalition at an escaping tie.  The note correctly retains the joint terminal
law and the complete response obstacles as separate graph coordinates.  It
must continue to say explicitly that those extra coordinates, rather than
the split marginals alone, retain relative timing.

## 2. Compact trace and restriction maps

For a genuinely finite set of labelled nodes, the ambient product in (14) is
compact and metrizable.  The closure of actual traces is therefore compact.
If “\(Q\) extends \(P\)” means literally that every actual execution of
\(Q\), after forgetting the new labels, is an actual execution of \(P\), then
coordinate projection gives

\[
\pi_{QP}(X_Q)\subseteq X_P
\]

and the projections compose.  Surjectivity is neither true nor needed.

There are three qualifications.

First, a boundary point of \(X_P\) is only a closed-graph record.  Its marginal
law, terminal law, obstacle and cap coordinates need not arise jointly from
one actual profile.  The note respects this in its passport discussion, but
the later phrase “strategic completeness” can be misread as executable
completeness of every point.  It is exact only on actual traces or after a
reconstruction passport is discharged.

Second, an obstacle records the payoff of every unilateral replacement, not
the entire successor trace by itself.  On an actual node, the retained
marginal laws plus coordinate overwrite do reconstruct that successor.  On a
boundary node, no such assertion follows without a passport.

Third, the claimed projective architecture is not yet fully specified.
“Program”, “actual legal execution”, “source port”, “regeneration witness” and
the extension relation need definitions.  A root obtained from an auxiliary
equation may vary discontinuously; recording the selected root as an input
parameter avoids a false selector theorem, but then stability is stability in
the enlarged trace/parameter space, not continuity of an endogenous root
selection.

## 3. Quantitative stability

The estimates (28)--(39) are valid with the note's full \(\ell^1\) convention.
In particular,

\[
\|\mu-\nu\|_1
\le \Delta_N(\mu,\nu)+\tau_\mu(N)+\tau_\nu(N)
\]

separates the Never atom from the late finite tail.  Product coupling then
gives the payoff and obstacle bounds, uniformly over all pure dates and Never,
and hence the cap bound.  The late-date approximation by \(\omega\) is also
correct.

The composed program estimate is valid only on the explicitly restricted
domain where:

- every suffix denominator has its stated positive lower bound;
- every input law has the stated finite-tail bound;
- every varying prefix, replacement law or selected root contributes its own
  parameter error; and
- no unrecorded discontinuous selector is part of the operation.

Under those conditions the construction genuinely avoids a single modulus
uniform over all calendar depths.  The modulus is selected only after the
finite program and its reach floors have been fixed, as required by the
question.

## 4. Tight-fusion reconstruction

Theorem 1 is correct after adding one omitted elementary inequality.  From
coordinatewise convergence, every finite partial mass of the proposed limit
is at most one.  Eventual tightness gives the reverse inequality in the limit,
so the finite atoms and Never atom sum to exactly one.  The note currently
proves only the reverse inequality explicitly.

The same tightness estimate then upgrades coordinatewise convergence to
total-variation convergence.  Fixed prefixing and replacement commute with
that limit.  Suffix conditioning commutes on a fixed positive-reach region.
Consequently every fixed previously requested node is realized by the one
reconstructed family of stopping laws.

This is best stated first as a precise stopping-law theorem, without the
passport vocabulary:

> For a countable increasing family of finitely many named ports, coordinate
> convergence plus portwise eventual uniform finite-tail tightness and
> positive conditioning floors yields one actual stopping-law packet; all
> fixed operations commute with the limit in total variation, and the full
> pure-time/Never response menus converge uniformly.

The terminal-Nash corollary is then correct.  If the prescribed payoffs
converge and every debt tends to zero, total-variation continuity of the full
response menu makes the reconstructed profile an exact terminal Nash profile.
This is a conditional consumer; it does not produce the required tight
vanishing-debt family from an arbitrary game.

## 5. Negative example

The two-player calculation is exact.  With the clock uniform on
\(\{0,\ldots,n-1\}\) and the tester playing Never,

\[
U=(-1,0),\qquad B_c=0,\qquad B_a=1/n.
\]

The split clock converges to \(\delta_\omega\), the cap tends to zero, and no
actual profile can realize the limiting semantic pair: payoff \(-1\) forces
the clock to stop finitely almost surely, every probability law on
\(\mathbb N\) then has a positive atom, and the tester can Quit at that atom.

The capacity lemma

\[
e\le \beta_\infty+\sum_n\beta_n
\]

is also exact.  With \(\sum_n\beta_n=1/2\), any actual attempted recovery of
the unit late atom has at most one half of its clock mass at finite dates, so
the clock payoff stays at least \(-1/2\).  This is a clean fixed-error
diagonal obstruction with the correct program-dependent spirit.

What is not yet proved in the note is the broad assertion that the displayed
family gives coherent traces for every operation admitted by the informal
program language.  That requires an induction on a defined grammar.  The
narrow theorem already suffices: the root program and its increasing finite
clock-coordinate probes are finitely compatible, while no actual diagonal
can meet the summable budget.  State that version rather than quantifying over
undefined regeneration and selector operations.

## 6. Existing results and novelty

The semantic nonattainment example is not new to the repository.  It is the
same clock/tester table and diffuse uniform-clock mechanism formalized in
`UniformEquilibrium/Diagnostics/Quitting/PositiveDebtTerminalSemanticNonattainment.lean`:

- `profile_semanticPair_tendsto_limitPair`;
- `limitPair_mem_carrier`; and
- `limitPair_not_mem_attainable`.

The existing theorem is already against arbitrary behavioral profiles and
unrestricted deviations.  The present note should cite it as the source of
the semantic core rather than present Theorem 4 as wholly new.

The repository also already contains much of the weak-law reconstruction and
cap-continuity infrastructure in
`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`,
notably:

- `quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile`;
- `eventually_forall_abs_quittingTerminalPayoff_update_pureTime_sub_lt`;
- `quittingContinuationBestResponseValue_compactStoppingLawProfile_tendsto`;
- `quittingTerminalSemanticPair_compactStoppingLawProfile_tendsto`; and
- `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit`.

Those results use the existing one-point compact clock and an opponent-tight
hypothesis that treats late-or-Never mass together.  The present proposal's
genuine additional organization is:

1. the split compactification that keeps Never separate from late-finite
   escape;
2. portwise finite-tail tight fusion giving total-variation reconstruction
   while allowing positive Never mass;
3. explicit finite-program conditioning moduli; and
4. the late-mass capacity/summable-budget formulation of the already checked
   semantic nonattainment example.

The compact split-clock response graph itself was already proposed in
`meta/STATE_TOPOLOGIES_AND_APPROXIMATION.md`; the new content is the proposed
fusion theorem and the quantitative recovery obstruction, not the bare state
space.

## 7. Strongest export-worthy package

The current capstone should be replaced by a narrower two-part packet.

### Positive theorem

Formalize split stopping laws and prove:

\[
\begin{array}{c}
\text{finite-atom and Never-coordinate convergence}\\
+\ \text{eventual uniform finite-tail tightness}
\end{array}
\Longrightarrow
\begin{array}{c}
\text{one actual total-variation limit}\\
+\ \text{uniform convergence of complete response menus and caps}\\
+\ \text{commutation with every fixed positive-reach finite program}.
\end{array}
\]

Add the exact-terminal-Nash corollary for vanishing debt.

### Negative theorem

For the checked clock/tester reward table, augment the existing semantic
nonattainment result with the split late atom and capacity estimate.  Prove
that every finite coordinate request is approximable, but no actual clock law
can satisfy the stated summable recovery budget and approximate the target
clock payoff within less than \(1/2\).

This pair is mathematically clean, directly addresses the maintained
question, and does not overstate the still-open producer problem.  It should
be independently reviewed after being extracted from the informal
architecture document.

## Re-audit of the revised theorem surface

The revised source note resolves the substantive scope objections above.

- It defines a finite rooted elementary-program grammar containing only fixed
  finite prefixing/concatenation, exogenous complete replacement, and
  fixed-depth positive-reach suffixing.
- It explicitly excludes regeneration, limit-witness, rank, and implicit
  root-selection edges unless a separate closed-limit or executable adapter is
  supplied.
- It distinguishes one initial port, which reconstructs one controller, from
  several initial ports, which reconstruct only one coherent packet.
- Its stability theorem now states the required tail bounds, reach floors, and
  operation-parameter errors.
- The tight-fusion proof now includes the missing upper bound on limiting
  total mass.
- The negative theorem's unconditional statement is narrowed to finite
  cylinder probes. Its extension is only to the defined elementary grammar on
  positive-reach domains, not to arbitrary regeneration or selectors.
- The conclusion says expressly that neither the non-elementary Fin4 adapters
  nor a tight vanishing-debt producer has been constructed.

I find no remaining broad mathematical overclaim in the revised scope. The
claim that the clock/tester sequence extends from root cylinders to each fixed
elementary program is a routine structural induction on the newly defined
grammar; an export should either include that induction or retain the already
sufficient cylinder-level theorem.

Two duplicated phrases remain as editorial artifacts (“For depth \(h\),
define” and “shows that all derived node laws are the literal laws obtained by
executing”). They do not affect the mathematics.
