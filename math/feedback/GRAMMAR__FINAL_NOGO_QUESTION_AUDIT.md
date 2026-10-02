# Final audit of the vanishing-reach no-go and compositional-state question

Targets:
[`VANISHING_REACH_SUFFIX_NO_GO.md`](../meta/VANISHING_REACH_SUFFIX_NO_GO.md)
and
[`QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`](../questions/QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md)

Reviewer: `GRAMMAR_FINAL_NOGO_QUESTION_AUDIT`

Verdict: `MATH_ACCEPTED`

## Round-two final signoff

The revised pair passes. This signoff supersedes the repair verdict in the
initial audit retained below.

The no-go now fixes the total-variation convention explicitly and proves the
exact identity

$$
\mathsf{CSR}_1
=
\{(\mu,S_1\mu):q_1(\mu)>0\}
\cup
\bigl(\{\delta_0\}\times\Delta(\mathbb N\sqcup\{\infty\})\bigr).
$$

Both inclusions are justified. Arbitrary fibre membership follows from the
delayed-law construction. Conversely, if the limiting reach is positive,
the conditioning estimate supplies a fixed positive-reach neighbourhood and
forces the target to be the literal suffix; if it is zero, the source must be
\(\delta_0\). The protected-source, unit-separation, reach-weighted nonclaim,
and law-intrinsic self-loop conclusions retain their exact narrow scopes.

The question now includes every repair requested below:

- initial and exogenous law coordinates have finite-coordinate and Never
  convergence plus eventual finite-tail tightness;
- persistent suffixes retain positive reach floors, and triangular decoders
  retain both fixed-column convergence and uniform tail summability;
- all other varying data have compact carriers or prescribed convergence;
- terminal Nash errors vanish against unrestricted behavioral deviations and
  terminal payoffs converge to one fixed target;
- the chronological-return output records actual source-attached finite
  chronologies, common endpoint convergence, vanishing seams, and a fixed
  positive certified gain;
- renewable exit is restricted to the dispatch-selected successor relation;
- a negative table supplies one rational \(\gamma>0\) against every behavioral
  profile and complete unilateral deviations; and
- the acceptable-negative answer fixes both one construction and one adapter
  class, including one specified ranked enlargement with its terminal and
  backward consumers.

In particular, the former \(\delta_m\) counterexample is excluded exactly by
the finite-tail tightness hypothesis. The repaired coherent-diagonal request
matches the sufficient theorem surface in `meta/GRAMMAR.md`.

The construction-facing instantiation remains genuinely open. The
vanishing-reach no-go is a valid boundary theorem but deliberately does not
exclude the alternative adapters admitted by the question. Both records are
timeless and contain no ephemera links or historical maintenance prose. I
find no unresolved mathematical or scope objection and give final
`MATH_ACCEPTED` signoff as ordinary mathematics, without a Lean or export
seal.

## Initial status (superseded)

The standalone no-go is mathematically correct at its stated narrow scope. Its
conditioning estimate, arbitrary zero-reach fibre, protected-source
reconstruction obstruction, unit conditional separation, and law-intrinsic
rank obstruction all pass independent calculation.

The maintained question does not yet pass literally. Its universal
subsequence request omits tightness and is false already for a diagram
consisting of one initial law port. Its acceptable-negative clause also
quantifies over an undefined class of ranked enlargements. These are defects
in the question surface, not defects in the no-go.

The intended construction-facing problem remains open. In particular, the
no-go explicitly leaves open reach-weighted consumers, finite-precision uses,
external phase ranks, and richer provenance, so it does not answer the
question's stronger negative alternative.

Both target records are timeless: neither contains edit history, migration
language, transient status, or a link or path to an ephemeral research
record. The no-go is presented as ordinary mathematics, not as a checked Lean
theorem.

## Claim checked

The no-go claims that closing the graph of depth-one positive-reach
conditioning creates arbitrary law-valued successors over the zero-reach
source \(\delta_0\). It then claims that \(\delta_\infty\) cannot be recovered
from that exact protected source by the listed elementary law operations, and
that the full closed relation admits no strictly decreasing natural-valued
rank depending only on the law.

The question asks for a finite two-sorted executable grammar, a coherent
diagonal theorem for increasing finite executions, and an instantiation that
produces a terminal, return, ranked-exit, or counterexample outcome.

All checks below are ordinary mathematics. I did not run or claim a new Lean
formalization.

## Independent check of the no-go

Use the probability convention

$$
d_{\mathrm{TV}}(\mu,\nu)
=\sup_A|\mu(A)-\nu(A)|
=\tfrac12\lVert\mu-\nu\rVert_1.
$$

Let \(A=\{d,d+1,\ldots,\infty\}\), \(a=\mu(A)\), and
\(b=\nu(A)\). For every event \(C\subseteq A\),

$$
\left|\frac{\mu(C)}a-\frac{\nu(C)}b\right|
\le \frac{|\mu(C)-\nu(C)|}{a}
   +\frac{\nu(C)|a-b|}{ab}
\le \frac{2d_{\mathrm{TV}}(\mu,\nu)}{\rho}
$$

when \(a,b\ge\rho>0\). Taking the supremum and shifting time proves the
displayed conditioning estimate. The example also proves that no modulus can
remain uniform over all positive reaches as the reach vanishes.

For an arbitrary stopping law \(\tau\), let \(L_1\tau\) delay every finite
date by one and fix Never, and set

$$
\mu_p=(1-p)\delta_0+pL_1\tau.
$$

Then

$$
d_{\mathrm{TV}}(\mu_p,\delta_0)=p,
\qquad q_1(\mu_p)=p,
\qquad S_1\mu_p=\tau.
$$

Thus every \((\delta_0,\tau)\) lies in the closed fibre, while none is a
legal positive-reach suffix execution at \(\delta_0\). The two displayed
specializations to \(\delta_0\) and \(\delta_\infty\) are exact, finitely
supported, and uniformly tight.

The protected-source invariant is also correct for the stated elementary
operations. If \(\mu(\infty)=0\), finite prefixing or block concatenation
multiplies this mass by the finite word's continuation probability, and a
legal suffix changes it to \(\mu(\infty)/q_d(\mu)=0\). With the sole law input
protected from complete replacement, induction over a finite program gives
\(\nu(\infty)=0\). Consequently

$$
d_{\mathrm{TV}}(\nu,\delta_\infty)=1.
$$

For the one-player reward \(1\) on quitting and \(0\) on Never,

$$
U(\nu)=1-\nu(\infty),\qquad B(\nu)=1.
$$

Hence the closed-relation target \(\delta_\infty\) and every faithful
protected recovery differ by one both in prescribed payoff and in terminal
exploitability gap. The note correctly confines this to the conditional
suffix: at the original source \(\mu_n^N\), the gap is only
\(p_n\to0\).

Finally, \(q_1(\delta_\infty)=1\) and
\(S_1\delta_\infty=\delta_\infty\), so the closed relation has the literal
self-loop \((\delta_\infty,\delta_\infty)\). No map from laws to
\(\mathbb N\) can strictly decrease on every such edge. This says nothing
against a rank on enlarged proof-relevant nodes, exactly as the note states.

One minor editorial improvement would be to define the convention for
\(d_{\mathrm{TV}}\). Equation (7) equals one under the half-\(L^1\) convention;
under the full \(L^1\) convention it equals two. The mathematics is otherwise
unambiguous.

## Counterexample to the question's compactness quantifier

Take the constant elementary diagram with one one-player initial port and no
edges. In its \(m\)-th execution put the root law

$$
\mu_m=\delta_m.
$$

The diagrams and their named ports are restriction-compatible, but for
\(m\ne n\),

$$
d_{\mathrm{TV}}(\delta_m,\delta_n)=1.
$$

Therefore the execution sequence has no total-variation convergent
subsequence. Pointwise compactification does not help: its escaping limit is
not an actual stopping law with the required law semantics.

The sentence beginning “Prove that every increasing,
restriction-compatible sequence” should instead quantify over one common
execution sequence satisfying the tight-fusion assumptions used by the
canonical grammar:

- finite-coordinate and Never-coordinate limits for every initial and
  exogenous law input;
- eventual finite-tail tightness for each persistent such input;
- a displayed eventual positive reach floor for every persistent suffix;
- compact carriers or prescribed convergence for every varying witness,
  branch tag, and error; and
- the fixed-column and uniform-tail hypotheses for every triangular decoder.

With these hypotheses the request is a meaningful sufficient-schema theorem;
without them it is a false compactness assertion.

## Remaining scope repairs to the question

The outcome clauses should retain the quantifiers consumed by the exact
semantic endpoints.

1. “Terminal approximate Nash profiles with one limiting payoff” should
   require errors tending to zero, terminal payoffs tending to one fixed
   target, and caps over unrestricted behavioral deviations.
2. A renewable exit should be asserted for the dispatch-selected successor
   relation, not every edge of a larger ambient legal graph.
3. A decisive finite-table certificate should supply one fixed
   \(\gamma>0\) such that every behavioral profile has some complete
   unilateral deviation gaining at least \(\gamma\).
4. “Positive admissible chronological return” needs either a self-contained
   definition in the question or a finite-data formulation of the return
   object and its consumer.

The acceptable-negative clause should quantify over one precisely defined
adapter class, or over one specifically proposed ranked enlargement with its
terminal and backward consumers. “Every proposed renewable ranked
enlargement” is not a fixed mathematical domain: an enlargement may add an
external use counter or other proof-relevant state. The current no-go
correctly does not claim this universal exclusion.

After these repairs, the question is still open and is not resolved by the
vanishing-reach example.

## Source audit

The exact declarations inspected were:

- `quittingUniformEquilibriumPayoffConjecture`
  (`UniformEquilibrium/Quitting/Conjecture/Basic.lean`), which is an open
  proposition definition;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`);
- `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  (`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`); and
- `StoppingLaw.toScalarHazard` and
  `StoppingLaw.stoppingLaw_toScalarHazard`
  (`MathUE/Probability/StoppingLawReconstruction.lean`), together with
  `quittingStoppingLawBehaviorStrategy` and
  `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy`
  (`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`).

The terminal endpoint confirms the needed unrestricted approximate-Nash
quantifier. The exploitability endpoint confirms that a negative solution
needs one fixed positive gap against every behavioral profile. The stopping
law declarations confirm actualizability of every law by a canonical live-spine
behavior, while also supporting the no-go's caution that a law does not retain
arbitrary off-path behavioral code once survival is zero.

## Suggested next move

Keep `VANISHING_REACH_SUFFIX_NO_GO.md` unchanged except for the optional TV
convention clarification. Repair the compactness and outcome quantifiers in
the question before continuing to list it as a fully self-contained open
question. The no-go should remain a scoped boundary result, not be promoted
as a negative answer to the repaired construction problem.

## Export assessment

The no-go has a complete exact ordinary-mathematics proof and a sharply stated
nonclaim, but this audit does not propose an export or a Lean seal. The
maintained question is not export material and needs the repairs above before
serving as a literal open-problem specification.
