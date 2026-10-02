# Nested terminal cap children transport one fixed outsider debtor

Authors: CODEX_SPINOZA

Independent reviews:
[CODEX_GROMOV](../feedback/CODEX_SPINOZA__NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT__BY_CODEX_GROMOV.md)
and
[CODEX_HAHN](../feedback/CODEX_SPINOZA__NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT__BY_CODEX_HAHN.md).

## Exact statement

Let \(I=\operatorname{Fin}4\), let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a bounded quitting reward table, and let Never pay zero. Choose \(M>0\)
such that every reward coordinate has absolute value at most \(M\).
Behavioral randomizations are independent across players and dates
conditional on public survival, and a unilateral deviator may replace their
complete behavioral strategy.

Assume the game has no uniform-equilibrium payoff, and fix a terminal
exploitability gap \(\Gamma>0\): at every actual behavioral profile some
player has an actual unilateral behavioral deviation with terminal-payoff
gain at least \(\Gamma\).

Suppose actual profiles \(\tau^n\) and independent product roots \(q^n\) are
given for \(n\ge0\), with

\[
 \tau^{n+1}=q^n::\tau^n.                                    \tag{1}
\]

Write

\[
 (U^n,B^n)=\operatorname{Sem}(\tau^n),\qquad
 h_{n,i}=q_i^n,\qquad
 c_n=\prod_i(1-h_{n,i}).                                    \tag{2}
\]

Assume:

1. \(q^n\) is exact root Nash against the literal continuation payoff \(U^n\);
2. \(c_n>0\) for every \(n\); and
3. the total marginal hazard is summable:

   \[
    \sum_n\sum_i h_{n,i}<\infty,\qquad
    C_\infty:=\prod_nc_n>0.                                 \tag{3}
   \]

Fix one player \(b\). Suppose player \(b\)'s complete unrestricted behavioral
cap at every \(\tau^n\) is attained by the deterministic clock \(A^n=n\).
Define the literal cap child

\[
 \zeta^n=\tau^n[b\leftarrow A^n].                            \tag{4}
\]

For each \(n\), obtain \(\bar q^n\) from \(q^n\) by forcing \(b\) to Continue
and retaining every outsider marginal:

\[
 \bar q_b^n=0,\qquad \bar q_i^n=q_i^n\quad(i\ne b).           \tag{5}
\]

Then the following conclusions hold.

### Literal nesting and killed owner

Every \(\zeta^n\) absorbs no later than date \(n\), and

\[
 d_b(\zeta^n)=0.                                             \tag{6}
\]

The children obey the exact actual-profile identity

\[
 \boxed{\zeta^{n+1}=\bar q^n::\zeta^n.}                      \tag{7}
\]

The joint Continue probability of \(\bar q^n\) is

\[
 \bar c_n=\prod_{i\ne b}(1-h_{n,i})\ge c_n.                 \tag{8}
\]

### One fixed outsider and one fixed response

Fix any depth \(R\). Since \(b\) Quits surely by date \(R\), every outsider's
complete cap at \(\zeta^R\) is attained among

\[
 \{0,1,\ldots,R,\operatorname{Never}\}.                     \tag{9}
\]

The terminal gap at \(\zeta^R\) therefore selects one player \(j\ne b\) and
an attained pure-time cap \(\beta_j\) whose actual gain is

\[
 g=d_j(\zeta^R)\ge\Gamma.                                   \tag{10}
\]

For \(N\ge R\), define a complete behavioral deviation \(\beta_j^N\) by
copying the prescribed \(j\)-marginal through the new roots
\(\bar q^{N-1},\ldots,\bar q^R\), then using \(\beta_j\) in the unchanged
suffix \(\zeta^R\). Its exact gain is

\[
\begin{aligned}
 &U_j(\zeta^N[j\leftarrow\beta_j^N])-U_j(\zeta^N)\\
 &\qquad =
 \left(\prod_{n=R}^{N-1}\bar c_n\right)
 \bigl(U_j(\zeta^R[j\leftarrow\beta_j])-U_j(\zeta^R)\bigr).
                                                                  \tag{11}
\end{aligned}
\]

Consequently the same fixed player is a debtor at every later child:

\[
 d_j(\zeta^N)\ge
 \left(\prod_{n=R}^{N-1}\bar c_n\right)\Gamma
 \ge C_\infty\Gamma
 \qquad(N\ge R).                                             \tag{12}
\]

Neither the label nor its actual behavioral response is reselected with
depth.

### Exact outsider cap-clock recursion

For each outsider, complete caps can be selected coherently across the
nested children. For the fixed \(j\), choose cap times \(T_{n,j}\) so that

\[
 T_{n+1,j}\in\{0,T_{n,j}+1\},                                \tag{13}
\]

where \(\operatorname{Never}+1=\operatorname{Never}\).
Thus exactly one of the following occurs:

- after finitely many front resets, one fixed old cap is shifted forever
  through the new roots; this includes the permanent-Never subcase; or
- reset to Quit0 occurs at arbitrarily large depths.

For finite selected times, the last-reset coordinate
\(R_{n,j}=n-T_{n,j}\) stays fixed under a shift and jumps to \(n+1\) under
a reset.

### Exact Bellman identity and outsider Nash seam

Let

\[
 W^n=U(\zeta^n),\qquad
 \Delta_i^n=W_i^n-U_i^n.                                    \tag{14}
\]

Equation (7) gives a literal Bellman chain:

\[
 W^{n+1}=F_{\bar q^n}(W^n).                                 \tag{15}
\]

Player \(b\)'s prescribed Continue action is root-Nash because its entire
strategy \(A^{n+1}\) attains the complete cap. Outsider root Nash does not
follow.

For \(i\ne b\), let \(Q_i,H_i,s_{n,i}\) be respectively the root Quit
endpoint, Continue absorbing numerator, and opponent Continue probability at
\(q^n\). Put bars over the corresponding quantities at \(\bar q^n\), and
write

\[
 \bar s_{n,i}=\prod_{\ell\ne i,b}(1-h_{n,\ell}).
\]

Subtracting the old Quit-minus-Continue gap from the new one gives exactly

\[
\begin{aligned}
 &\bigl[\bar Q_i-(\bar H_i+\bar s_{n,i}W_i^n)\bigr]
  -\bigl[Q_i-(H_i+s_{n,i}U_i^n)\bigr]\\
 &\qquad =
  (\bar Q_i-Q_i)-(\bar H_i-H_i)
  -\bar s_{n,i}\Delta_i^n
  -(\bar s_{n,i}-s_{n,i})U_i^n.                              \tag{16}
\end{aligned}
\]

The first, second, and fourth terms are bounded by a reward-box constant
times \(h_{n,b}\), hence form summable sequences. The third term need not be
summable: \(\bar s_{n,i}\to1\), while the hypotheses do not force
\(\Delta_i^n\to0\). Positive far-end reach permits an order-one displacement.
Thus (15) is Bellman-exact but is not an exact or known summably approximate
Nash--Bellman spine.

## Conjecture-facing change

The positive-survival exact-cap-clock theorem gives, at each depth, one
terminal cap child and a new terminal-gap debtor. Taken separately, those
children appeared to permit the debtor label and response to change
arbitrarily with depth.

This result proves literal projective coherence. The cap children form one
nested actual genealogy, and a single outsider response selected once
retains gain at least \(C_\infty\Gamma\) forever. It also gives the exact
reset-versus-shift recursion for that outsider's complete cap.

Therefore label coherence and source ancestry are no longer missing in this
branch of
[FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md).
The remaining obstruction is the explicit cross-coordinate payoff seam
\(\Delta_i^n\) in (16). The theorem does not consume that seam.

## Definitions and assumptions

The complete cap is

\[
 B_i(\sigma)=
 \sup_{\beta_i}
 U_i(\sigma[i\leftarrow\beta_i]),
\]

where \(\beta_i\) ranges over all behavioral strategies, including
calendar-dependent randomization, every finite pure stopping time, and
literal Never. The debt is
\(d_i(\sigma)=B_i(\sigma)-U_i(\sigma)\).

The prefix \(q::\tau\) plays the independent product root \(q\) at the
current public date and uses \(\tau\) after joint Continue. The strategy
\(\beta_j^N\) in (11) is behavioral: it copies the prescribed mixed action
at every new public date and changes only the reached suffix strategy.

For the endpoint notation in (16),

\[
 C_i(q_{-i};v_i)=H_i(q_{-i})+s_i(q)v_i.
\]

Thus \(H_i\) includes the absorbing reward contribution when \(i\) Continues
and some opponent Quits, while \(s_i(q)\) is the probability that every
opponent Continues.

The summability in (3) is not an extra arbitrary-game hypothesis in the
intended adapter. Under no uniform payoff it is supplied by checked bounded
finite exact-block capacity for the positive-survival reverse-prefix
recursion.

## Source correspondence

The positive-survival source comes from the reviewed chain

\[
 \text{tropical two-Never source}
 \longrightarrow
 \text{cap-pinned paid source}
 \longrightarrow
 \text{positive-survival first exact root}.
\]

The existing exports are
[FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md](FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md),
[FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md](FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md),
and
[FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET.md](FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET.md).

Iterating literal exact roots in the positive-survival arm gives (1)--(3) and
the exact clocks \(A^n\). The capacity input is
finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff in
UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean.
The true chronological exact blocks are
\(q^{N-1},\ldots,q^0\), with values
\(U^N,\ldots,U^0\).

The payoff factorization in (11) is the iterated
root-then-continuation identity. Behavioral-to-pure-time reduction and finite
cap attainment use the stopping-law expectation identity; after \(b\) stops
surely by \(R\), all pure times after \(R\) are outcome-equivalent to Never.

The reviewed source note is
[CODEX_SPINOZA__NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT.md](../notes/CODEX_SPINOZA__NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT.md),
frozen at SHA-256
6d813418986400654a0c93fd8e54469b9d965fd61fdefee848cf7c9803c9e956.
The two independent reviews above checked the literal genealogy, complete
behavioral transport, cap recursion, exact seam, and nonconsumer.

## Proof

### Literal nesting

By definition,

\[
 \tau^{n+1}=q^n::\tau^n.
\]

The clock \(A^{n+1}\) forces \(b\) to Continue at the new root and then uses
\(A^n\) in the old suffix. Replacing \(b\)'s whole strategy therefore
changes exactly \(q_b^n\) to zero and \(\tau_b^n\) to \(A^n\), proving (7).
Equation (8) follows from the definitions.

The prescribed strategy \(A^n\) is an attained complete cap against the
unchanged opponents. Updating a player to an attained cap leaves that
player's cap value unchanged and makes its debt zero, proving (6). Sure Quit
at date \(n\) proves terminality by that date.

### Fixed-observer transport

At \(\zeta^R\), sure termination by \(b\)'s clock makes the outsider response
problem finite up to the Never equivalence class. Apply the terminal gap and
then choose the attaining cap of its observer. Equation (6) rules out
\(b\), proving (9)--(10).

At every root before \(\zeta^R\), the prescribed and deviating \(j\)-actions
have the same distribution. On every root-absorbing event their complete
play therefore agrees. Only joint Continue reaches the changed suffix.
One use of the exact root-then-continuation payoff identity multiplies the
old gain by \(\bar c_n\). Induction gives (11).

By (8) and (3),

\[
 \prod_{n=R}^{N-1}\bar c_n
 \ge\prod_{n=R}^{N-1}c_n
 \ge C_\infty.
\]

The complete cap dominates the constructed deviation, proving (12).

### Cap-clock recursion

At the new root in \(\zeta^{n+1}\), any pure-time response by \(j\) either
Quits now or Continues and then uses a pure-time response in \(\zeta^n\).
The best value in the second class is attained by a selected cap at
\(\zeta^n\). Select a maximizing branch and its corresponding time.
This proves (13), including the Never convention.

If resets stop, repeated shifts retain the last selected cap forever. If the
selected cap is Never, shifting leaves it Never. If resets do not stop, they
occur at arbitrarily large depths. The last-reset statement is immediate.

### Outsider seam

Equation (15) is the prescribed-payoff identity for the literal prefix (7).
For \(b\), its prescribed whole strategy is cap-attaining, so Quit now cannot
improve upon prescribed Continue followed by the old cap.

For \(i\ne b\), its own marginal is unchanged between \(q^n\) and
\(\bar q^n\). Expanding the two Continue endpoints as absorbing numerator
plus opponent Continue mass times tail payoff and subtracting gives (16).

Only events in which \(b\) Quits at the old root contribute to
\(\bar Q_i-Q_i\), \(\bar H_i-H_i\), and
\(\bar s_{n,i}-s_{n,i}\). Their probability is at most \(h_{n,b}\), and all
payoffs are bounded. These three terms are therefore bounded by a fixed
multiple of \(Mh_{n,b}\) and are summable by (3). No analogous estimate
controls \(\Delta_i^n\), whose coefficient tends to one. This proves the
stated seam and nonconsumer.

## Boundary tests

### Terminal by a deadline is not finite-clock complete semantics

Although \(\zeta^n\) terminates under prescribed play by date \(n\), outsider
strategies may retain positive hazards at arbitrarily late counterfactual
dates. Those histories become reachable if \(b\) changes its own strategy
and can change \(B_b\) by order one. Hence the child is not automatically an
IsQuittingFiniteClockProfile or QuittingDeadlineBounded source.

### Fixed debtor transport does not return to the old exact-root genealogy

The response in (11) is profitable at \(\zeta^N\), not at \(\tau^N\).
Transporting it back changes the opponent strategy of \(b\). A unilateral
\(j\)-deviation cannot condition on the counterfactual event that \(b\)
first switches to its cap.

### Positive source reach does not make the seam small

Positive far-end reach means a far-end change of \(b\)'s strategy remains
visible with positive weight. It can therefore sustain an order-one
\(\Delta_i^n\). Replacing that positive reach by a small-error estimate
reverses the meaning of (3).

### The cap-clock descriptor is not a decreasing rank

The last-reset coordinate remains constant under a shift and jumps upward
under a reset. Permanent Never is a valid eventual-shift arm. No
well-founded descent follows from (13).

### Punishment-floor exact tails are separately re-solved

A floor-safe child starts the checked summable marked exact orbit. An
underfloor child with positive debt starts an exact dynamic-debt tail whose
joint absorption is summable by
summable_dynamicDebtTailAbsorptionCharge_of_floorViolation_of_positiveDebt.
Those exact roots are selected against their own successor payoffs and need
not equal the roots \(\bar q^n\) in (7). The floor split therefore gives no
return identity.

## Adapter and consumer

The actual-data adapter is the infinite positive-survival branch of the
recursive exact cap-clock construction. Every \(\tau^n\), \(q^n\), \(A^n\),
and \(\zeta^n\) is retained definitionally. Checked bounded capacity supplies
(3), and the terminal gap supplies one observer at one finite child.

The output resolves two previously missing fields:

- all children lie on one literal genealogy; and
- one fixed outsider and one fixed complete behavioral response retain a
  uniform positive gain along that genealogy.

No named existing consumer accepts the remaining object. The genealogy roots
are Bellman-exact, but outsiders need not be root-Nash because of (16).
Finite-clock consumers require bounded individual stopping laws and often a
minimum source; adjacent-deadline consumers require supplied finite timing
Nash laws; exact-spine consumers require exact or summably approximate root
Nash. The theorem supplies none of those missing hypotheses.

Thus the exact surviving obligation is to consume or cancel
\(\Delta_i^n\), not to reselect a debtor or reconstruct source ancestry.

## Lean handoff

A narrow formalization should use four declarations.

1. FinFourEscapingCapClock.nestedTerminalChildren: retain (4)--(8)
   definitionally.
2. FinFourNestedCapChildren.transportBehavioralDeviation: prove (11) by
   iterated root-then-continuation factorization and return the fixed observer
   debt floor (12).
3. FinFourNestedCapChildren.exists_coherentPureTimeCaps: use sure termination
   by \(b\) to prove finite cap attainment and the reset/shift recursion
   (13), with Never explicit.
4. FinFourNestedCapChildren.outsiderRootGap_sub: formalize (16) using
   Quit payoff, Continue absorbing numerator, and opponent Continue mass.

The terminal-gap observer must be selected only after finite cap attainment
at \(\zeta^R\). The transport theorem should accept a complete behavioral
deviation and copy its root marginals; it must not replace that deviation by
a stationary strategy. The outsider seam must remain a conclusion, not be
assumed summable.

## Scope and nonclaims

This is reviewed ordinary mathematics, not yet Lean-checked.

The theorem proves a literal nested child sequence, a fixed outsider debt
floor, a fixed transported behavioral response, and an exact reset/shift cap
classification. It does not prove that \(\bar q^n\) is root-Nash for
outsiders, that its Nash defect is summable, or that the child sequence is an
accepted exact spine.

It does not transport the fixed debtor back to \(\tau^N\), identify a
semantic return, or construct a decreasing finite rank. The child is terminal
under prescribed play but need not have finite-clock complete semantics.

The theorem does not produce a terminal approximate Nash profile, a
source-reprojected return, or a uniform-equilibrium payoff. It narrows the
positive-survival branch to the explicit cross-coordinate seam (16).
