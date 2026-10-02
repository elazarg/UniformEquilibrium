# Positive-survival exact prefixes renew a cap only as an escaping clock

Authors: CODEX_SPINOZA

Independent reviews:
[CODEX_HAHN](../feedback/CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL__BY_CODEX_HAHN.md)
and
[CODEX_NEGATIVE_CERTIFICATE](../feedback/CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL__BY_CODEX_NEGATIVE_CERTIFICATE.md).

## Exact statement

Let \(I=\operatorname{Fin}4\), and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a bounded quitting reward table. Choose \(M>0\) such that
\(|r_i(S)|\le M\) for every terminal coalition and player. Never pays zero. Behavioral
randomizations are independent across players and dates conditional on public
survival, and a unilateral deviator may replace their complete behavioral
strategy.

Assume the game has no uniform-equilibrium payoff. Fix \(\Gamma>0\) such that
every actual behavioral profile admits a unilateral terminal-payoff gain of
at least \(\Gamma\); such a gap exists under the preceding assumption. Fix an
actual behavioral profile \(\tau^0\), a player \(b\), and a number
\(\gamma>0\). Write

\[
 (U^0,B^0)=\operatorname{Sem}(\tau^0),\qquad
 d_{0,i}=B_i^0-U_i^0.
\]

Suppose literal Quit at date zero, denoted \(A^0\), attains player \(b\)'s
complete unrestricted behavioral cap at \(\tau^0\), and

\[
 d_{0,b}\ge\gamma.                                           \tag{1}
\]

Recursively, at every \(n\ge0\), choose an arbitrary exact independent
product Nash root \(q^n\) against the literal prescribed continuation payoff
\(U^n\), and define

\[
 \tau^{n+1}=q^n::\tau^n,\qquad
 (U^{n+1},B^{n+1})=\operatorname{Sem}(\tau^{n+1}),\qquad
 d_{n+1,i}=B_i^{n+1}-U_i^{n+1}.                              \tag{2}
\]

Put

\[
 h_{n,i}=q_i^n,\qquad
 c_n=\prod_{i\in I}(1-h_{n,i}),\qquad
 s_{n,b}=\prod_{i\ne b}(1-h_{n,i}).                          \tag{3}
\]

This packet concerns the positive-survival branch

\[
 c_n>0\qquad\text{for every }n.                              \tag{4}
\]

Define \(A^{n+1}\) to force \(b\) to Continue at the newest root and,
conditional on joint Continue, to use \(A^n\) in the old tail. Thus \(A^n\)
is the literal deterministic quit time \(n\) in \(\tau^n\).

Then all the following conclusions hold.

1. For every \(n\), \(A^n\) attains player \(b\)'s complete unrestricted
   behavioral cap at \(\tau^n\), and

   \[
    d_{n+1,b}=s_{n,b}d_{n,b},\qquad
    d_{N,b}=d_{0,b}\prod_{n<N}s_{n,b}.                       \tag{5}
   \]

2. At the newest prefix there is a second executable response which copies
   \(b\)'s prescribed root marginal and, after joint Continue, uses \(A^n\).
   Its exact gain is

   \[
    c_nd_{n,b}=(1-h_{n,b})d_{n+1,b}.                         \tag{6}
   \]

   After installing this copied response, player \(b\)'s residual complete
   debt is exactly

   \[
    h_{n,b}d_{n+1,b}.                                        \tag{7}
   \]

   If \(h_{n,b}>0\), this is also the exact current-root support-Nash defect.

3. There is a finite constant \(K\), depending only on the reward table,
   such that for every \(N\ge1\),

   \[
    \sum_{n<N}\sum_{i\in I}h_{n,i}\le K.                     \tag{8}
   \]

   Consequently,

   \[
    \sum_{n=0}^{\infty}\sum_i h_{n,i}<\infty,\qquad
    C_\infty:=\prod_{n=0}^{\infty}c_n>0.                     \tag{9}
   \]

   The old actual source \(\tau^0\) is entered through each finite
   reverse-prefix word with probability at least \(C_\infty\). Every fixed
   marked row inside that suffix keeps its conditional data, and its original
   total reach is multiplied by a factor at least \(C_\infty\). Moreover

   \[
    d_{N,b}\ge C_\infty d_{0,b}\ge C_\infty\gamma.           \tag{10}
   \]

4. For every \(N\), the literal cap child

   \[
    \zeta^N=\tau^N[b\leftarrow A^N]                          \tag{11}
   \]

   absorbs no later than date \(N\), gains at least
   \(C_\infty\gamma\) for \(b\), and satisfies

   \[
    d_b(\zeta^N)=0.                                          \tag{12}
   \]

   The terminal gap at \(\zeta^N\) is witnessed by a player \(j_N\ne b\).
   The witness can be reduced to a pure-time response in

   \[
    \{0,1,\ldots,N,\operatorname{Never}\}.                   \tag{13}
   \]

   Comparing it with a pure-time component of the prescribed strategy yields
   a literal paid first-disagreement row of gain \(\Gamma\), with cut at most
   \(N\). That row's opponent live mass is at least \(\Gamma/(2M)\).

5. The prescribed payoff sequence is Cauchy. Writing its limit as
   \(U^\infty\), every fixed front window of the
   chronological blocks converges to

   \[
    (U^\infty,\operatorname{allContinue}),
    (U^\infty,\operatorname{allContinue}),\ldots .           \tag{14}
   \]

   All Continue is an exact root against \(U^\infty\), and its Bellman action
   fixes \(U^\infty\). Thus the front limit is the exact all-Continue phantom;
   the source mark and the cap time remain only at the far end of blocks whose
   lengths tend to infinity.

## Conjecture-facing change

The positive-survival arm of
[FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET.md](FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET.md)
previously retained one delayed paid response after the first exact root but
did not classify repeated exact prefixing.

This result identifies the whole infinite positive-survival branch. The
complete cap does renew exactly and the original marked source does retain
uniformly positive reach. However, the cap renews only by moving one date
farther into the future at every prefix. Checked finite exact-block capacity
forces the surrounding total root hazard to be summable. Consequently every
fixed front window loses the source mark and converges to the all-Continue
phantom.

This strictly narrows the positive-survival branch of
[FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md):
the remaining object is a source-marked, all-summable reverse block with an
escaping exact cap clock. The theorem does not consume that object into a
uniform equilibrium.

## Definitions and assumptions

For an actual profile \(\sigma\),

\[
 U_i(\sigma)=\text{its prescribed terminal payoff},\qquad
 B_i(\sigma)=\sup_{\beta_i}
 U_i(\sigma[i\leftarrow\beta_i]),
\]

where the supremum ranges over every unilateral behavioral strategy, including
calendar-dependent randomization, every finite pure stopping time, and literal
Never. The debt is \(d_i(\sigma)=B_i(\sigma)-U_i(\sigma)\).

The prefix \(q::\tau\) plays the independent product Quit/Continue root \(q\)
at the current public date and uses \(\tau\) after joint Continue. Exact root
Nash means that every player's prescribed root marginal is a best response
between Quit and Continue against the other root marginals and the literal
continuation payoff \(U(\tau)\). It does not mean that the entire prefixed
profile is terminal Nash.

For player \(b\), \(s_{n,b}\) is the probability that all opponents Continue
at root \(q^n\), and \(c_n=(1-h_{n,b})s_{n,b}\) is joint Continue
probability. Assumption (4) implies every marginal has positive Continue
probability.

No compact limiting profile is substituted for any \(\tau^n\). Every prefix,
cap update, stopping time, and paid-row source in the statement is literal.

## Source correspondence

The arbitrary-game source is the reviewed chain

\[
 \text{tropical two-Never source}
 \longrightarrow
 \text{off-minimum stationary paid port}
 \longrightarrow
 \text{first exact root}.
\]

Its first two stages are
[FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md](FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md)
and the cap-pinned source used by
[FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md](FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md).
The exact survival split is
[FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET.md](FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET.md).
In its positive-survival arm, choose one sufficiently late literal stationary
source and use it as \(\tau^0\). The theorem here applies conditionally for
as long as the recursive exact roots all have positive joint survival. It
does not assert that every recursive selection stays in this arm.

The exact prefix/debt semantics are supported by
quittingTerminalSemanticDebt_prefix_eq_blockAct and
quittingTerminalSemanticPrefix_mem_carrier in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean.
The capacity input is
finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff
in
UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean.
It applies to finite exact Nash--Bellman blocks in the canonical
quittingNashBellmanBox; it requires no punishment-floor or reachability
field.

The terminal-gap input is
not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
in UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean.
Behavioral-to-pure-time reduction uses
quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime, and the paid
row uses the checked first-disagreement construction. The finite response set
in (13) is a consequence of the literal sure quit by \(b\), not of a
bounded-controller restriction.

The reviewed mathematical source is
[CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL.md](../notes/CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL.md),
frozen at SHA-256
3823bb3e816de7d3328b0a82045dae42daae9f3cd3a937b7b50bf7a3370052ee.
The two reviews above independently reconstructed the complete result in this
packet.

## Proof

### Exact cap-clock transport

Fix \(n\). Since \(c_n>0\), player \(b\) has positive Continue probability
at the newest root. Let \(Q_b(q^n_{-b})\) and
\(C_b(q^n_{-b};U_b^n)\) be its root Quit and Continue endpoints. Exact root
Nash gives

\[
 Q_b(q^n_{-b})\le C_b(q^n_{-b};U_b^n),                      \tag{15}
\]

with equality if \(h_{n,b}>0\).

Replacing the old tail payoff \(U_b^n\) by its complete cap \(B_b^n\) raises
only the Continue endpoint, and raises it by exactly
\(s_{n,b}d_{n,b}>0\). Therefore the complete cap at the prefixed profile is
the branch that Continues at the newest root and then uses \(A^n\). The
prescribed prefixed payoff equals the old Continue endpoint: this is immediate
when \(h_{n,b}=0\), and follows from indifference when \(h_{n,b}>0\).
Subtracting proves

\[
 d_{n+1,b}=s_{n,b}d_{n,b}.
\]

It also proves that \(A^{n+1}\) attains the unrestricted cap. Induction,
starting from the supplied \(A^0\), proves (5).

The copied response preserves every root-absorbing outcome. Only joint
Continue, of exact probability \(c_n\), exposes the old tail improvement
\(d_{n,b}\); hence its gain is \(c_nd_{n,b}\). Replacing \(b\)'s own strategy
does not change its opponents and therefore leaves its complete cap invariant.
Subtracting the copied-response gain from the new debt gives

\[
 d_{n+1,b}-c_nd_{n,b}
 =h_{n,b}s_{n,b}d_{n,b}
 =h_{n,b}d_{n+1,b},
\]

which proves (6)--(7). When \(h_{n,b}>0\), old exactness ties the two root
endpoints at \(U_b^n\), whereas the cap-tail replacement strictly raises only
Continue. The same quantity is therefore the exact support defect.

### Reverse blocks and bounded capacity

For each \(N\), read the literal profile \(\tau^N\) in its true chronological
order:

\[
 q^{N-1},q^{N-2},\ldots,q^0,\tau^0.                         \tag{16}
\]

The displayed continuation values are
\(U^N,U^{N-1},\ldots,U^0\). At root \(q^n\), literal prefixing gives the
Bellman identity with predecessor \(U^{n+1}\) and continuation \(U^n\), and
\(q^n\) is exact Nash against \(U^n\). Every actual terminal payoff lies in
the canonical reward box. Thus (16) is a finite exact Nash--Bellman block,
and its hazard charge is exactly

\[
 \sum_{n<N}\sum_i h_{n,i}.
\]

The checked counterexample-side Fin4 capacity theorem supplies one uniform
finite \(K\), proving (8). Monotone partial sums give the series in (9).
Every \(h_{n,i}<1\) by (4); the standard positive-product criterion then
gives \(C_\infty>0\).

The probability of reaching the old suffix through (16) is
\(\prod_{n<N}c_n\ge C_\infty\). Also \(s_{n,b}\ge c_n\), so (5) gives

\[
 d_{N,b}\ge d_{0,b}\prod_{n<N}c_n
 \ge C_\infty d_{0,b}\ge C_\infty\gamma.
\]

This proves (8)--(10).

### Terminal cap children and paid rows

The strategy \(A^N\) Quits surely at absolute date \(N\) in \(\tau^N\).
Consequently \(\zeta^N\) is terminal by date \(N\). Since \(A^N\) attains
the complete cap, the update gains \(d_{N,b}\) and kills \(b\)'s debt exactly,
proving (11)--(12).

Apply the terminal exploitability gap at the literal profile \(\zeta^N\).
It supplies an actual behavioral deviation of gain at least \(\Gamma\).
Because \(d_b(\zeta^N)=0\), its observer \(j_N\) is distinct from \(b\).
Against opponents that surely absorb by date \(N\), every pure quit time
strictly after \(N\) is payoff-equivalent to Never, while time \(N\) retains
its simultaneous-quit endpoint. The unrestricted pure-time response
supremum is therefore a maximum over (13).

The stopping-law expectation identity expresses both the deviating and the
prescribed behavioral payoffs as expectations of pure-time payoffs.
Support-pair averaging selects a response time and a prescribed support time
whose payoff difference is at least \(\Gamma\). Their first-disagreement
decomposition gives the stated paid row; positivity forces its cut to be at
most \(N\). A row of gain \(\Gamma\) is bounded above by
\(2M\) times its opponent live mass, proving the final assertion in item 4.

### The front phantom

One prefix changes each prescribed coordinate by at most

\[
 |U_i^{n+1}-U_i^n|
 \le2M(1-c_n)
 \le2M\sum_j h_{n,j}.                                       \tag{17}
\]

The series in (9) makes \(U^n\) Cauchy. It also implies
\(h_{n,i}\to0\) for every player, so \(q^n\) tends to all Continue.
Continuity of the finite root Nash defects shows that all Continue is exact
against \(U^\infty\), and its Bellman action fixes \(U^\infty\).
Equation (14) follows for every fixed front window of (16).

## Boundary tests

### Positive survival is essential

If some \(c_n=0\), the cap-clock induction above cannot use a positive
Continue probability for every player. The reviewed first-root theorem has
a separate unique-sure reset at its original source, and
[FIN4_UNIQUE_SURE_ROOT_SAME_PROFILE_SINGLETON_HANDOFF.md](FIN4_UNIQUE_SURE_ROOT_SAME_PROFILE_SINGLETON_HANDOFF.md)
consumes its same-profile limiting reset. This packet neither identifies nor
renews an arbitrary later zero-survival descendant.

### The copied response is not an exact root repair

Equation (7) is an exact falsifier. Whenever \(h_{n,b}>0\), installing the
copied delayed response leaves positive \(b\)-debt and makes Continue strictly
better than Quit on a prescribed positive-quit support. Positive reach to
the old cap therefore does not by itself create a Nash--Bellman edge.

### A terminal child is not a bounded-deadline Nash profile

The child \(\zeta^N\) absorbs surely by date \(N\) because \(b\) uses \(A^N\),
but the other players retain the nonstationary reverse-prefix tail. Their
old root inequalities need not survive the cap update. Thus \(\zeta^N\) is
not asserted to be terminal Nash, an exact finite-clock law, or a
QuittingDeadlineBounded source.

### Front convergence loses the marked source

The far-end reach is at least \(C_\infty\) in every finite block, but the
far end moves to calendar time \(N\). Local convergence at every fixed date
therefore yields the all-Continue profile and can lose all terminal mass.
This is the moving-deadline discontinuity, not a contradiction to positive
finite-block reach.

### A cap update need not preserve outsider root Nash

If replacing \(b\)'s old tail changes outsider \(i\)'s tail payoff by
\(\Delta_i\), then, with the newest root fixed, \(i\)'s Quit-minus-Continue
gap changes by exactly

\[
 -s_{n,i}\Delta_i.                                          \tag{18}
\]

The source data control neither its sign nor its size. Forcing \(b\) to
Continue at the newest root additionally changes the current opponent law.
Hence cap transport alone does not reproject an exact source.

## Adapter and consumer

The exact input adapter is the positive-survival side of the reviewed first
exact-root packet, whose cap-pinned stationary source comes from the tropical
two-Never chain. Starting with one literal source \(\tau^0\), choose exact
roots and prefix them to the actual descendant. If all roots retain positive
joint survival, the present theorem applies. Every finite word is accepted
by the checked canonical-box finite exact-block capacity theorem.

The output is a complete reduction, not a terminal consumer:

\[
 \boxed{\text{positive-survival recursive exact roots}
 \Longrightarrow
 \text{bounded-charge reverse blocks with an escaping exact cap clock}.}
\]

It preserves one fixed actual source at uniformly positive far-end reach,
one fixed player's full behavioral cap, and a fixed positive debt floor for
that player. The terminal child additionally produces a literal finite-cut
paid row. No checked consumer combines those fields while retaining the
exact Nash--Bellman chronology. Existing forward-spine consumers require a
finite-date persistent mark or a source-compatible return; adjacent-deadline
consumers require re-solved finite timing Nash laws. Neither hypothesis is
produced here.

## Lean handoff

A narrow formalization can separate four declarations.

1. QuittingPositiveSurvivalExactCapClock: by induction, Continue followed by
   an attained tail cap is the new complete cap, with (5).
2. QuittingPositiveSurvivalCopiedCapResponse: prove the exact gain, residual
   debt, and support defect in (6)--(7).
3. FinFourPositiveSurvivalRecursivePrefix.exists_boundedHazard_and_sourceReach:
   assemble the reverse chronological word as a
   QuittingFiniteExactNashBellmanBlock in
   quittingNashBellmanBox (quittingRewardBound reward) and invoke
   finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff.
4. FinFourPositiveSurvivalRecursivePrefix.terminalCapChild: retain
   \(\tau^N,A^N,\zeta^N\) definitionally and package the terminal-gap
   observer, finite pure-time witnesses, and paid first-disagreement row.

The capacity declaration should not acquire a punishment-floor or
reachability hypothesis. The cap-clock declaration must quantify over the
complete behavioral cap, not only current root actions. The paid-row wrapper
should select the terminal-gap observer and both pure-time witnesses jointly,
rather than fix an arbitrary debt label first.

## Scope and nonclaims

This is reviewed ordinary mathematics, not yet Lean-checked.

The theorem is conditional on the infinite positive-survival branch (4). It
does not say all exact-root selections remain in that branch. It does not
preserve stationarity after the first prefix, move the cap clock back to date
zero, or regenerate the original cap pin.

The finite blocks are exact Nash--Bellman blocks only in their true reverse
chronological order. The terminal cap children are actual profiles and their
deviations are unrestricted, but the children are not claimed to be Nash.

The positive far-end reach is not a finite-date atom in the front limit. No
source-reprojected return, punishment-floor orbit, renewable rank, terminal
approximate equilibrium, or uniform-equilibrium payoff is proved.
