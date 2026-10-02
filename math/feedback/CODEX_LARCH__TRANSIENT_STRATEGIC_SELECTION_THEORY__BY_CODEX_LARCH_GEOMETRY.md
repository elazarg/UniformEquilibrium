# Review of transient strategic selection

Reviewer: CODEX_LARCH_GEOMETRY. Date: 2026-09-07.

I independently reviewed the fixed-point and composition arguments in
[the transient selection sketch](../notes/CODEX_LARCH__TRANSIENT_STRATEGIC_SELECTION_THEORY.md).
The proposed special-class theorem passes this ordinary-mathematical review.
No Lean compilation or independent repository coverage audit was performed.

The all-joint-action inequality on h implies Eτ≤K for every history-dependent
profile, not just every stationary profile. Stopping the telescoping sum at
τ∧T handles unbounded exit times. The same estimate supplies the uniform
tail bound needed for continuity of the stationary terminal-value map.

The Kakutani construction is correctly formulated at the state/player action
level. At a fixed point, the prescribed action distribution is supported on
maximizers of the one-step continuation expression. Its own mixture equals
wᵢ(s) by the prescribed Bellman equation, so every alternative action is
bounded above by wᵢ(s). This produces a supermartingale inequality under
arbitrary unilateral behavior. It does not require an unjustified concavity
claim for a player's whole stationary policy. Almost-sure exit and bounded
continuation rewards justify passing from the stopped inequality to the
terminal cap.

For finite-horizon composition, condition on the public exit history and
literal exit state c. The parent's deviating suffix is an admissible child
deviation; no optimization or expectation is interchanged. For each realized
τ≤T, subtract the same vᵢ(c) from prefix rewards and suffix rewards. The
prefix costs at most 2Mτ/T. Suffixes shorter than Hδ cost at most 2MHδ/T,
while longer ones satisfy the chosen child accuracy after conditioning on
their entry history. For τ>T, the difference from the eventual terminal
target is at most 2M, charged to 2M min(τ,T)/T. Taking expectations gives
the stated δ+2M(K+Hδ)/T bound, and the deviated terminal-selection law is
then controlled by the Bellman cap. The target and stationary selector were
fixed before δ, preserving the required UE quantifier order.

The geometric matching-pennies example fits the hypotheses. The Stay-forever
example correctly identifies why prescribed absorption is insufficient.
Potential nonclosure of the child state region causes no problem because
the strategy can remember that the first exit occurred and permanently use
the child's original-game continuation strategy.

One optional clarification: assume X nonempty when defining max_X h, or
declare the empty selection region a trivial case. This is a minor statement
boundary, not a mathematical objection to the nonempty theorem.

The result supplies a genuine strategic selector under the common duration
hypothesis. It remains a structural special case: that hypothesis fails for
the unrestricted all-Continue action in a quitting game, and this review
does not promote it to a general UE argument.
