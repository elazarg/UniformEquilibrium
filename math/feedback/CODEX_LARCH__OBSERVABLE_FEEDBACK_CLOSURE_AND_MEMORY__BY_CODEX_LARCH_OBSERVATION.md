# Review of observable feedback closure and memory

Reviewer: CODEX_LARCH_ROUND2_OBSERVATION. Ordinary-mathematical independent
review, 2026-09-07; no Lean compilation.

The [feedback-closure sketch](../notes/CODEX_LARCH__OBSERVABLE_FEEDBACK_CLOSURE_AND_MEMORY.md)
passes review. I checked the row-switch equivalence, finite minimal closure,
and four-state full-memory counterexample. No unresolved mathematical
objection was found.

The baseline is itself admissible because each row belongs to the relevant
convex action hull. Replacing a single row is also admissible under the
stated independent row-choice policy class. The difference operator really
is the singleton indicator e_s times the scalar action-row difference.
Thus one nonzero retained scalar at that state forces e_s into an invariant
space. If every such scalar vanishes, the corresponding row is harmless.
Summing these row operators proves sufficiency for arbitrary randomized
state feedback. The proof would fail for controls constrained to a common
global action, and the note states that boundary explicitly.

Closure under P and the finitely many rank-one row-switch operators is
equivalent to closure under every admissible feedback matrix. The increasing
subspace algorithm therefore returns the smallest such space containing the
supplied outputs and constants, with at most |S| strict dimension increases.
Products of time-dependent Markov feedback matrices preserve it, so the
claimed prediction equivalence is valid for a common fixed Markov policy.

In the four-state example, P e_c=1−e_d and P e_d=e_d. Switching the c row
changes e_c by −e_c and e_d by e_c, both in W. Thus the complete feedback
criterion holds. Initial states a and b have the same retained evaluation.
The common full-history policy legitimately remembers which initial state
occurred, however, and selects different actions upon reaching c. Its two
compressed histories are identical, so this is precisely failure of policy
descent. At date two the stated e_d discrepancy is one. W already being a
partition algebra does not remove the discarded historical information.

The example concerns preserving the same strategy identifier, not a
comparison of optimized values; the note avoids that conflation. The
adjacent action-invisibility theorem remains valid for arbitrary history
policies because action choice has no effect on retained conditional
expectations, eliminating the memory channel used by this counterexample.

This is a substantive, compact extension of the controlled-observability
theory: it explains the distinction between linear closure for Markov
feedback and actual controlled-history quotient assumptions. It is not a
new equilibrium result or a complete strategy-factorization theorem.
