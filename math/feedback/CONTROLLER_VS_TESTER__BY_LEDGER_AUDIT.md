# Adversarial audit of `CONTROLLER_VS_TESTER.md`, Sections 1--4

## Claim audited

The audited claim is that one quitting-game behavior profile can be represented
by a finite-dimensional forward ledger which records its prescribed payoff and
its complete unrestricted behavioral best-response caps, including `Never`;
that the tester has an exact infinite occupation-flow primal and a bounded
Bellman dual with a `Never` transversality condition; and that finite controller
words followed by all Continue are semantically dense in the entire terminal-
semantic carrier.

I audited only Sections 1--4.  In particular, this is not a review of the
uniform-horizon and barrier claims in Sections 5--6.

## Verdict

The mathematical claims in Sections 1--4 survive.  I found no counterexample
to the ledger, the unrestricted-cap formula, the occupation-flow formulation,
the semantic prefix map, or finite-word density.

There is one real proof-presentation gap: the proposed strong-duality proof by
"choosing a maximizing branch" of the infinite Bellman recursion is not by
itself justified in an undiscounted infinite stopping problem.  The theorem is
nevertheless correct and has a shorter exact repair: Section 1 identifies the
cap with the supremum over pure finite stopping times and `Never`, and each of
those choices is literally a feasible occupation flow.  This proves the
missing reverse inequality without any infinite greedy-policy argument.

Two smaller closure steps should also be written explicitly: passage from
actual profiles to carrier points in the finite-word density proof, and the
padding argument which makes exact-length finite-word minima decrease.  Both
are immediate once stated and require no new hypothesis.

## 1. Forward ledger

For a prescribed row sequence \(x^0,x^1,\ldots\), the updates in (1) are
correct.  More explicitly,

\[
S_t=\prod_{s<t}c(x^s),\qquad
Y_{k,t}=\sum_{s<t}S_s g_k(x^s),
\]

and, for a deviating player \(i\),

\[
L_{i,t}=\prod_{s<t}\chi_i(x^s),\qquad
P_{i,t}=\sum_{s<t}L_{i,s}a_i(x^s).
\]

Thus \(P_{i,t}\) is exactly the payoff already accumulated when player \(i\)
has continued and its opponents absorb before date \(t\).  The value of first
quitting at \(t\) is

\[
P_{i,t}+L_{i,t}q_i(x^t),
\]

and the value of `Never` is \(P_{i,\infty}\).  Initializing \(M_i\) at \(-R\)
is a valid finite sentinel because every terminal payoff is at least \(-R\).
Consequently

\[
M_{i,\infty}
=\sup_t\bigl(P_{i,t}+L_{i,t}q_i(x^t)\bigr).
\]

The claimed bounds are also correct, with the slightly stronger weighted
bounds

\[
|Y_{k,t}|\le R(1-S_t),\qquad
|P_{i,t}|\le R(1-L_{i,t}).
\]

They follow from

\[
|g_k(x)|\le R(1-c(x)),\qquad
|a_i(x)|\le R(1-\chi_i(x)),
\]

and exact hazard telescopes.  Candidate quit values satisfy

\[
|P_{i,t}+L_{i,t}q_i(x^t)|\le R,
\]

so \(M_i\) is also bounded.  The reachable-state closure is therefore compact;
its invariance under a fixed legal update follows from continuity of that
update.

The prescribed series and each opponent-absorption series converge absolutely.
The nonabsorbing event has terminal payoff zero, so \(U=Y_\infty\).

## 2. Full behavioral cap, including `Never`

The cap identity (5) is exact.  At the sole live public history on each date,
a unilateral behavioral replacement is completely described, for payoff
purposes, by its first stopping time in
\(\mathbb N\cup\{\infty\}\).  Its payoff is the expectation of the pure-time
values.  Conversely, a probability law on this compactified countable set is
implemented by its conditional hazards.  If the remaining tail mass in the
displayed hazard formula is zero, the subsequent hazards are arbitrary because
those dates are unreachable; this harmless convention should be stated.

Thus taking arbitrary time dependence, private behavioral randomization,
arbitrarily late stopping, and `Never` does not enlarge the supremum beyond

\[
\max\left\{
\sup_t(P_{i,t}+L_{i,t}q_i(x^t)),\ P_{i,\infty}
\right\}.
\]

This is independently supported by the checked declarations
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean` and
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

## 3. Occupation-flow primal and transversality dual

The flow equations (7) are exact rather than a relaxation.  If \(y_t\) is the
mass with both the tester and all its opponents still live, then \(s_t\) is the
tester-quit part, \(k_t\) is the tester-continue part, and

\[
y_{t+1}=\chi_tk_t.
\]

Conversely \(h_t=s_t/y_t\) reconstructs the hazards whenever \(y_t>0\);
when \(y_t=0\), both \(s_t\) and \(k_t\) vanish.  The residual mass at infinity
is the joint nonabsorbing event and contributes zero.  Absolute convergence of
the objective follows from

\[
\sum_ts_t\le1,
\qquad
\sum_tk_t(1-\chi_t)\le1,
\qquad
|a_t|\le R(1-\chi_t).
\]

Weak duality is correct, but one small sign argument is implicit.  Induction
gives \(0\le y_t\le L_t\).  For bounded \(w_t\),

\[
y_tw_t\ge \min\{0,L_tw_t\}.
\]

Hence \(\liminf L_tw_t\ge0\) really does imply
\(\liminf y_tw_t\ge0\), even when some \(w_t\) are negative.  This justifies
passing to the limit in (12).

For the actual tail value

\[
w_t=\sup\{\hbox{pure-time values from tail }t,\ \hbox{Never value}\},
\]

the Bellman equality (13) holds and \(w\) is bounded.  Its transversality is
also correct.  If \(L_t\to0\), it follows by boundedness.  If
\(L_t\to L_\infty>0\), the conditional probability of any later opponent
absorption under `Never` equals

\[
1-\frac{L_\infty}{L_t}\longrightarrow0.
\]

The tail-`Never` payoff therefore tends to zero, while \(w_t\) dominates that
payoff, giving \(\liminf w_t\ge0\).

### Required repair to strong duality

The sentence asserting equality by choosing a maximizing branch at every date
should be removed or proved separately.  Local maximization in an infinite
undiscounted recursion does not automatically control the residual boundary
term and need not produce an attaining policy.

The exact repair is simpler.  Section 1 gives

\[
w_0=B_i(\sigma)=\sup_{\theta\in\mathbb N\cup\{\infty\}}V_i(\theta).
\]

Each deterministic \(\theta\) produces a feasible flow whose objective is
exactly \(V_i(\theta)\).  Therefore the primal supremum is at least \(w_0\).
Weak duality and feasibility of the actual tail-value sequence give

\[
\sup_{\mathrm{flows}}\mathcal P_i
\le \inf_{w\ \mathrm{dual}}w_0
\le B_i(\sigma)=w_0,
\]

so all three quantities are equal.  This handles unattained suprema without
an approximate greedy construction.

The finite-window version with terminal cap \(\beta\) is then the standard
finite backward induction and is exact, provided \(\beta\) denotes the actual
continuation cap attached to that window, as the text intends.

## 4. MPC endpoint and semantic prefix

For a finite word followed by perpetual all Continue, (15) is exact:

\[
\widehat U_i=Y_i,
\qquad
\widehat B_i=\max\{M_i,P_i+L_i\max(r_i(\{i\}),0)\}.
\]

The two tail alternatives are quitting alone at any finite later date and
`Never`.  Hence the finite-word objective tests the complete behavioral class,
not merely deviations confined to the optimization window.  Continuity of the
ledger update and compactness of \([0,1]^{I\times m}\) imply attainment of each
finite minimum.

The semantic prefix map (19) agrees with the checked
`quittingTerminalSemanticPrefix`: prescribed payoff is the absorbing root
contribution plus joint survival times the tail payoff, while a deviator chooses
between quitting now and continuing into its unrestricted tail cap.  Its
continuity and preservation of the carrier are checked by
`continuous_quittingTerminalSemanticPrefix` and
`quittingTerminalSemanticPrefix_mem_carrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.

## 5. Finite-word density

The truncation proof is correct, including its treatment of the only delicate
boundary.  The truncated cap converges to

\[
\max\{\sup_tQ_t,\ P_\infty+L_\infty s_i^+\}.
\]

If \(L_\infty s_i^+=0\), this is the original cap.  Otherwise
\(L_\infty>0\) and \(s_i>0\).  Convergence of the positive product implies
\(\chi_i(x^t)\to1\), and

\[
|q_i(x^t)-s_i|\le2R(1-\chi_i(x^t))\to0.
\]

Consequently

\[
Q_t\to P_\infty+L_\infty s_i,
\]

so the apparent extra boundary value is already dominated by the supremum of
genuine finite stopping-date values.  This is exactly the point at which a
naive finite-horizon Bellman truncation would otherwise lose `Never`.

To finish (21) formally, the text should add one closure sentence.  The
argument first proves that every *actual* semantic pair belongs to the closure
of the finite-word pairs.  Taking closures then gives the same inclusion for
the carrier, which is the closure of the actual pairs.  The reverse inclusion
uses that every finite-word pair is actual and the carrier is closed.

The stronger quantitative version is independently checked in the Research
lane: `exists_cofinalFiniteClockSemanticPair_sequence_tendsto` and
`closure_quittingCofinalFiniteClockSemanticPairs_eq_carrier` in
`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`.  Those theorems use
canonical quantile supports and retain literal finite-clock realizers; the
elementary truncation argument here is sufficient for the unquantified closure
identity.

Finally, the monotonicity and limit assertion in (24) needs the following
explicit padding observation.  Appending one all-Continue row to the *end* of
a finite word followed by the all-Continue tail changes no semantic pair.
Thus the exact-length reachable sets are nested after this padding, their
continuous-objective minima decrease, and the infimum over their union equals
the minimum over its compact closure.  This proves the stated decreasing
limit.

## Final assessment

Sections 1--4 provide a valid finite-dimensional sufficient information state
for evaluating one fixed controller chronology against every behavioral
tester, and a valid complete finite-word approximation of the terminal-
semantic carrier.  They do not, by themselves, synthesize a low-debt
chronology or decide whether the minimum exploitability is zero.  Their value
is exact representation and finite approximation, not a solution of the
producer problem.

The only substantive correction required inside the audited scope is to
replace the infinite greedy-branch sentence by the pure-time-flow proof of
strong duality above.  The other omissions are routine closure and padding
details.
