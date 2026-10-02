# Endogenous soft cyclic blocks: terminal Nash or isolated-owner escape

Authors: `CODEX_SPINOZA`

Independent reviews:
[CODEX_SNELL](../feedback/CODEX_SPINOZA__ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE__BY_CODEX_SNELL.md),
[CODEX_NEGATIVE_CERTIFICATE](../feedback/CODEX_SPINOZA__ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE__BY_CODEX_NEGATIVE_CERTIFICATE.md)

## Exact statement

Let \(I=\operatorname{Fin}4\), and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I,
 \qquad |r_i(S)|\le M.
\]

Never pays zero.  Behavioral randomization is independent across players and
dates, conditional on public survival.  A unilateral deviation replaces one
complete behavioral strategy and may Quit at any finite date or Never.  All
payoffs below are undiscounted terminal payoffs.

For every integer \(H\ge1\) and every \(\varepsilon>0\), there are product
roots

\[
 x_0,\ldots,x_{H-1}\in(0,1)^I
\]

and phase values

\[
 v_0,\ldots,v_{H-1}\in[-M,M]^I
\]

(indices modulo \(H\)) such that the cyclic Bellman equations hold exactly,

\[
 v_t=F(x_t,v_{t+1}),                                    \tag{1}
\]

and every playerwise root Nash defect is at most \(\varepsilon\).  Repeating
the word forever gives an actual almost-surely absorbing behavioral profile
\(\sigma^{H,\varepsilon}\), whose terminal payoff from phase \(t\) is exactly
\(v_t\).

For player \(i\), set

\[
 c_{t,i}=\prod_{j\ne i}(1-x_{t,j}),\qquad
 P_i=\prod_{t<H}c_{t,i},\qquad A_i^-=1-P_i.             \tag{2}
\]

Then \(A_i^->0\), and the unrestricted terminal deviation debt satisfies

\[
 d_i(\sigma^{H,\varepsilon})
 \le {H\varepsilon\over A_i^-}.                        \tag{3}
\]

Consequently, if a sequence of these profiles satisfies

\[
 \max_i {H_n\varepsilon_n\over A_{n,i}^-}\longrightarrow0, \tag{4}
\]

then a subsequence has \(v_{n,0}\to v\), terminal exploitability tends to
zero, and this particular \(v\) is a uniform-equilibrium payoff.

Conversely, suppose every actual behavioral profile has maximum terminal
debt at least \(\Gamma>0\).  For any \(H_n,\varepsilon_n\) with
\(H_n\varepsilon_n\to0\), a subsequence has one fixed player \(i\) such that

\[
 A_{n,i}^-\le {H_n\varepsilon_n\over\Gamma}\to0.       \tag{5}
\]

Writing

\[
 A_{n,i}^+=1-\prod_{t<H_n}(1-x_{n,t,i}),                \tag{6}
\]

one of two arms remains after a further subsequence.

1. If \(A_{n,i}^+\ge a>0\), the terminal coalition law converges to the point
   mass on \(\{i\}\), \(v_{n,0}\to r(\{i\})\), and every outsider's debt
   tends to zero.  The owner's debt may remain positive through normalized
   rare-opponent continuation.
2. If \(A_{n,i}^+\to0\), then

   \[
   \sum_{t<H_n}\sum_jx_{n,t,j}\longrightarrow0.        \tag{7}
   \]

   Thus the output is a vanishing-hazard cyclic Nash--Bellman packet with
   exact return, but the theorem does not assert that its aggregate support
   error is little-o of its hazard.

For fixed \(H\) and \(\varepsilon_n\downarrow0\), the same argument gives an
exact cyclic Nash--Bellman limit in which every player other than one fixed
\(i\) Continues surely at every phase.  This exact limit may be all Continue
or isolated-\(i\); it need not itself be a terminal Nash profile.

## Conjecture-facing change

This is an unconditional finite-dimensional producer for every Fin4 quitting
table.  It replaces a falsely imposed zero terminal boundary by an
endogenous cyclic boundary: roots and successor values are solved jointly,
and the repeated word is an actual terminal profile.  Its deviation estimate
is against unrestricted behavioral deviations, not only root, stationary,
or bounded-clock deviations.

It strictly narrows the two live questions
[`FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md)
and
[`FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md`](../archive/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md):
either the produced player-deleted absorption dominates its row error and
directly gives a fixed uniform payoff, or a hypothetical counterexample must
admit the explicit isolated-owner escape (5), followed by exactly the two
arms above.  The result does not consume those two arms.

## Definitions and assumptions

Fix a continuation vector \(w\in[-M,M]^I\) and a product root
\(x\in[0,1]^I\), where \(x_i\) is player \(i\)'s Quit probability.  With the
other coordinates fixed, let \(Q_i(x_{-i})\) be player \(i\)'s payoff from
Quit.  Define the Continue absorbing contribution by

\[
 D_i(x_{-i})=
 \sum_{\varnothing\ne S\subseteq I\setminus\{i\}}
   \Pr_{x_{-i}}(S\text{ is exactly the opponent quitter set})\,r_i(S).
                                                               \tag{8}
\]

Then the Continue endpoint and prescribed Bellman value are

\[
 C_i(x_{-i},w)=D_i(x_{-i})+
       \Bigl(\prod_{j\ne i}(1-x_j)\Bigr)w_i,             \tag{9}
\]

\[
 F_i(x,w)=x_iQ_i(x_{-i})+(1-x_i)C_i(x_{-i},w).          \tag{10}
\]

These expressions are continuous and lie in \([-M,M]\).  For temperature
\(\theta>0\), define the soft Quit response

\[
 L_i^\theta(x_{-i},w)=
 {e^{Q_i(x_{-i})/\theta}\over
  e^{Q_i(x_{-i})/\theta}+e^{C_i(x_{-i},w)/\theta}}.     \tag{11}
\]

It lies strictly between zero and one.  If
\(x_i=L_i^\theta(x_{-i},w)\), the elementary binary entropy bound gives

\[
 \max\{Q_i,C_i\}-F_i(x,w)\le\theta\log2.               \tag{12}
\]

This is the ordinary two-action Nash defect.  No regularized payoff is used
in the quitting game.

## Source correspondence

The finite Nash--Bellman path type is in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanMinimizer.lean`.
Exact cyclic objects and terminal compilers are in
`UniformEquilibrium/Quitting/Cycles/AdmissibleCycleTerminalEquilibrium.lean`.
The scalar companion contraction and its player-deleted survival factor are
in `CycleMismatchContraction.lean`; the equality-one/isolation boundary is in
`CycleIsolatedCoordinate.lean`, especially
`isQuittingIsolatedWindow_iff_opponentSurvivalWeight_eq_one`.

Behavioral pure-time completeness is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`BehaviorPureTimeExtremality.lean`.  The fixed-target terminal limit theorem
is `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`TerminalUniformPayoffSelection.lean`.

The checked relative-error consumer is
`hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample` in
`UniformEquilibrium/Diagnostics/Quitting/FourPlayerReturnedBlockGap.lean`.
The singleton-face consumer is
`QuittingTerminalExploitabilityWitness.singletonTight_atomicHandoff_or_playerDeletion`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonTightMinimumFaceIteration.lean`.

The new mathematics is the simultaneous Brouwer solution for the endogenous
cyclic boundary and soft roots, followed by the complete periodic cap
estimate (3).  No inspected declaration already produces these objects for
arbitrary \(H\) and \(\varepsilon\).

## Proof

### Soft cyclic producer

Put \(\theta=\varepsilon/\log2\).  On the compact convex set

\[
 \mathcal X=([0,1]^I)^H\times([-M,M]^I)^H
\]

define a continuous self-map by

\[
 x'_{t,i}=L_i^\theta((x_t)_{-i},v_{t+1}),\qquad
 v'_t=F(x_t,v_{t+1}).                                  \tag{13}
\]

The Bellman map preserves the reward box because every coordinate is a
convex combination of coalition rewards and the continuation coordinate.
Brouwer gives a fixed point.  Equations (1) and the row-error assertion
follow from (12)--(13), while (11) makes every root strictly interior.

Let

\[
 P=\prod_{t<H}\prod_{i\in I}(1-x_{t,i})<1.             \tag{14}
\]

One traversal has Bellman form \(a+Pv_0\), while exact return says
\(v_0=a+Pv_0\).  Infinite repetition has Never probability
\(\lim_NP^N=0\); geometric unrolling identifies its actual terminal payoff
with \(v_0\).  Phase shifts give every \(v_t\).

### Complete terminal-deviation estimate

Fix player \(i\).  Let \(W_{t,i}\) be its unrestricted terminal cap from
phase \(t\) against the periodic opponents and put
\(\delta_{t,i}=W_{t,i}-(v_t)_i\ge0\).  Pure-time extremality, equivalently
the scalar stopping Bellman equation, gives

\[
 W_{t,i}=\max\{Q_i((x_t)_{-i}),
              D_i((x_t)_{-i})+c_{t,i}W_{t+1,i}\}.      \tag{15}
\]

Here \(D_i\) is exactly (8), so
\(D_i((x_t)_{-i})+c_{t,i}(v_{t+1})_i\) is the prescribed Continue endpoint.
The row defect therefore yields

\[
 \delta_{t,i}\le\varepsilon+c_{t,i}\delta_{t+1,i}.    \tag{16}
\]

Iterating once around the period gives

\[
 \delta_{0,i}\le H\varepsilon+P_i\delta_{0,i}.
\]

Strict interiority gives \(P_i<1\), so rearrangement proves (3).  The same
argument works at every phase.  Equation (15) takes the supremum over every
finite stopping time and Never, hence covers arbitrary behavioral
deviations.

### Fixed target and positive-gap escape

Under (4), all four terminal debts tend to zero.  Compactness gives a
subsequence \(v_{n,0}\to v\), and
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` applies to
these actual profiles and payoffs, proving that this \(v\) is a uniform-
equilibrium payoff with the required fixed-payoff, uniform-horizon
quantifiers.

Under the gap \(\Gamma\), choose at each actual periodic profile a player
\(i_n\) with debt at least \(\Gamma\).  Formula (3) gives (5) for \(i_n\).
Stabilize the label among four players.  Every single opponent's period
absorption is at most \(A_{n,i}^-\), and compactness gives a fixed payoff
target subsequence.

For fixed \(H\) and \(\varepsilon_n\downarrow0\), phasewise compactness and
continuity give an exact cyclic Nash--Bellman limit.  Formula (5) makes the
product of every opponent's Continue factors tend to one, hence every such
factor tends to one.  Only the fixed player \(i\) may retain Quit mass.  The
resulting all-Continue or isolated-\(i\) cycle is exactly the exceptional
deleted-survival-one case isolated in the checked cycle files; it need not
be terminal Nash.

### The two arms

Suppose \(A_{n,i}^+\ge a>0\).  Within one period, every absorbing outcome
other than singleton \(i\) requires at least one opponent of \(i\) to Quit,
so its probability is at most \(A_{n,i}^-\).  Total period absorption is at
least \(A_{n,i}^+\ge a\).  Repetition normalizes the one-period absorbing
law, proving convergence to \(\delta_{\{i\}}\) and hence
\(v_{n,0}\to r(\{i\})\).  For outsider \(j\ne i\), its opponents include
\(i\), so \(A_{n,j}^-\ge A_{n,i}^+\ge a\).  Formula (3) makes its debt tend
to zero.  The owner's cap remains uncontrolled because its deleted-survival
factor tends to one.

If instead \(A_{n,i}^+\to0\), full joint survival through a period tends to
one.  Since \(-\log(1-q)\ge q\) for \(0\le q<1\), taking negative logarithms
of the finite survival product proves (7).  Exact return remains, but the
row error estimate alone does not give error little-o of this total hazard.

## Boundary tests

### Moving-period singleton diffusion

Punishment normality alone cannot turn the singleton arm into a fixed
collision deviation.  Fix distinct players \(i,j\), \(H\ge2\), and
\(\Gamma>0\).  Let \(r_j(\{i,j\})=\Gamma\) and every other reward coordinate
be zero.  Every player is punishment-normal.  Let only \(i\) Quit, with
hazard \(1/H\) at every phase of an \(H\)-periodic word.  Repetition absorbs
almost surely at \(\{i\}\), and one-period owner absorption is

\[
 1-(1-1/H)^H\ge1/2.                                    \tag{17}
\]

Player \(j\)'s deviation to absolute time \(n\) gains exactly

\[
 {\Gamma\over H}(1-1/H)^n\le\Gamma/H,                 \tag{18}
\]

because only a tie pays positively.  Never gains zero, and pure-time
extremality gives the same upper bound for every behavioral deviation.
This table has the all-Never equilibrium; it refutes only a direct inference
from punishment normality and a static collision premium, not the full
positive-gap hypothesis.

### Total absorption cannot replace opponent absorption

For every \(H\), take player \(0\) to Quit surely only at phase \(H-1\) and
let players \(1,2,3\) always Continue.  Pay player \(k\) \(-1\) exactly when
\(k\) belongs to the first quitting coalition, and zero otherwise.  With
cyclic continuation \(v=(-1,0,0,0)\), this is exact Nash--Bellman: player
\(0\) receives \(-1\) from every finite Quit time and continuation, while an
outsider receives zero by Continue and \(-1\) by Quit.  The word has total
absorption one and fixed payoff \(v\) for every \(H\).

Nevertheless player \(0\)'s Never deviation pays zero, so its terminal debt
is one and \(A_0^-=0\).  Thus exact endogenous boundary, exact root Nash,
sure absorption, and a fixed target do not imply terminal Nash when one
coordinate is isolated.  This example also has global minimum zero, so it is
a boundary test rather than a counterexample to the conjecture.

## Adapter and consumer

The actual-data adapter is unconditional: insert the given finite reward
table, \(H\), and \(\varepsilon\) into (13); Brouwer supplies the cyclic word,
and repetition is its literal behavioral profile.  No carrier source,
selected local root, or unrelated continuation is assumed.

There are three downstream interfaces.

1. If (4) holds, the checked fixed-target theorem immediately consumes the
   actual terminal profiles and their convergent payoffs.
2. In the singleton arm, a semantic subsequential limit has carrier
   membership, positive unique owner debt, owner singleton tightness, and
   zero outsider debt.  These are all the algebraic fields of
   `QuittingSingletonTightMinimumFace` except its global carrier-minimum
   field.  Minimum-fibre anchoring is the exact missing adapter to the checked
   atomic-handoff/player-deletion consumer.
3. In the diffuse arm, the word is already a literal
   `QuittingReturnedProductBlock`, with Bellman error zero.  Its checked
   aggregate `endpointRegret` is the sum of the actual two-action defects.
   The returned-block tangent theorem would consume the sequence if this
   regret were little-o of total hazard.  The stronger
   \(H_n\varepsilon_n=o(\sum_{t,i}x_{n,t,i})\) is sufficient but not proved.
   Under a hypothetical counterexample, the checked ambient gap instead
   forces endpoint regret at least a fixed positive multiple of hazard.

The two residual interfaces are genuinely different: minimum-fibre
anchoring in the singleton arm, and a positive relative-regret certificate
in the diffuse arm.  Neither is silently converted into a paid port.

## Lean handoff

A narrow formalization can proceed in four layers.

1. Define the finite-dimensional soft-response map on the existing simplex
   root and payoff boxes, prove the binary entropy estimate (12), and invoke
   Brouwer.
2. Package the fixed point as an existing cyclic/returned product block and
   prove its repeated-profile payoff by the one-period geometric identity.
3. Use `sSup_range_quittingTerminalPayoff_update_eq_pureTime` to formalize
   (15)--(16), then derive (3) from the cyclic product \(P_i\).
4. Apply
   `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` for the
   direct arm, and expose the two residual adapters using the existing
   singleton-tight-face and returned-block structures.

Useful finite tests are \(H=1\), where
\(\delta\le\varepsilon+c\delta\), and \(H=2\), where
\(\delta_0\le\varepsilon+c_0\varepsilon+c_0c_1\delta_0\).  The two boundary
tables above should be retained as regression tests for the deleted-survival
denominator and moving-period collision diffusion.

## Scope and nonclaims

- The roots are approximate Nash roots but the Bellman equations and cyclic
  return are exact.
- The repeated profile is actual and almost surely absorbing; no public
  correlation or artificial terminal payoff is used.
- The cap estimate covers Never and arbitrarily late behavioral deviations.
- The theorem does not produce exact roots, a bounded-period theorem, or a
  terminal approximate Nash profile in either escape arm.
- The singleton law limit does not identify the owner's cap with the cap of
  the literal pure-singleton profile.
- The diffuse arm does not supply regret little-o of total hazard.
- The theorem does not decide the Fin4 conjecture; it reduces failure of the
  direct terminal limit to the two explicit unconsumed arms above.
