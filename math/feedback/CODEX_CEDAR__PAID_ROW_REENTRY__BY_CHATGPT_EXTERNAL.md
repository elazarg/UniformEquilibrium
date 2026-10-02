# External assessment of the paid near-return target, with a scalar obstruction

Provenance: produced by an external ChatGPT session (not a conference
agent), relayed by the conference owner, checked by the orchestrator
against the repository before filing. It engages the formalizer question
`questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md` and this notebook's
branch; it was produced without sight of this notebook, so agreements
below are independent convergence, filed as feedback because the
overlapping content already lives here.

## Independent convergence (no new claims)

The external analysis re-derives, independently: the
exactification/re-entry decomposition of the open producer (this
notebook's framing); the necessity of changing the root or continuation
(the literal paid root-tail pair has positive endpoint-Nash defect,
exact edges force zero — Section 10 here); the `L >= g/(2M)` survival
bound and the decisive distinction that it bounds reached
observer-deleted survival mass, not the absorption charge of any exact
Nash-Bellman edge — so none of `c = L`, `c = g`, `c = g/(2M)` is
justified by the paid-row estimate alone; and the
diagonal-vanishing-endpoint compactness normalization (both endpoint
payoffs of the tolerance-indexed paths converge to one common limit in
the canonical box).

## Additions worth recording

1. **Diagonal-closure form of the target.** With
   `H_c = { (payoff(s), payoff(t)) : s -> t a finite exact R-path with
   some edge of charge >= c }` and `D` the diagonal, the question's
   conclusion is exactly: there exists `c > 0` with
   `closure(H_c) meets D`. Forward: tolerances `1/n` plus compactness of
   the payoff box; converse immediate. This is the cleanest statement of
   the open producer and shows the common-limit normalization is free.
2. **Charged payoff systole.** Define
   `delta(c) = inf { max_i |payoff(t)(i) - payoff(s)(i)| : s -> t an
   exact admissible path containing an edge of charge >= c }`. The
   target is exactly: there exists `c > 0` with `delta(c) = 0`. The
   sharp consequence for the negative direction: a genuine refutation
   must prove `delta(c) > 0` for EVERY `c > 0` compatible with the paid
   realization; refuting recurrence of any particular edge, root, or
   state establishes nothing about `delta(c)`.
3. **Charged-ray recurrence lemma, and why it cannot apply.** If one
   infinite exact admissible path contains infinitely many edges of
   charge `>= c`, compactness of the payoff box already yields
   `closure(H_c) meets D` (two charged indices with `eta`-close
   payoffs; the segment between them carries a charged edge). Under a
   terminal-counterexample witness this is vacuous: exact paths carry a
   common finite charge budget, so prefixes of total charge `N c` for
   all `N` are impossible, and the tolerance-indexed VARYING-path family
   is essential — each tolerance may start in a different
   high-potential region. Compactness gives recurrence exactly when
   fixed-charge events are concatenable, and the paid data supplies
   neither concatenability nor exact events.
4. **Question-file wording (for the formalizers).** The line "this is
   the weakest currently checked paid output" is accurate as "the
   weakest CONCRETE PATH-LEVEL output currently checked":
   `PaidFirstDisagreementUniformPayoffConsumer`
   (`UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`)
   is logically weaker still, but asks only for the final existence
   statement and is not an informative producer interface.

## Status

Items 1-3 are elementary and orchestrator-checked (ordinary
mathematics, not checked in Lean; the compactness steps use only the
bounded canonical payoff box). None of this bridges the paid branch:
the open hinge remains a quantitative source-matched exact
Nashification plus payoff re-entry theorem converting fixed behavioral
gain into a fixed absorption threshold without preserving the
profitable non-Nash root-tail fiber. No objection to any claim in this
notebook.
