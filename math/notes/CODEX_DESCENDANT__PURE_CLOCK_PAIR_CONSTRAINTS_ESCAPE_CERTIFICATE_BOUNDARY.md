# Pure-clock cycles and strategic pairs are filters, not counterexample certificates

Author: `CODEX_DESCENDANT`

## Status

**Exact regression and certificate-boundary result.**  A rational Fin4 table
satisfies a literal max-debt pure-clock response cycle and the strategic-pair
terminal obstruction, and it also lies in the checked residual-hard/full-core
nonstationary class.  Nevertheless it has an exact behavioral period-two
terminal Nash profile and a uniform-equilibrium payoff.  Thus these finite
local constraints do not imply a positive all-behavior exploitability gap.

The missing condition is precise: one must exclude an escape-compatible
sequence of finite-clock profiles whose unrestricted exploitability tends to
zero.  Semantically this is an infinite uniform-separation condition.  For a
fixed normalized rational table it is nevertheless finitely compressible when
true: the existing exact-scale hierarchy eventually emits an independently
verifiable lower tree.  No rational positive-gap table or lower tree is
produced here.

## 1. Question

Can the two surviving finite objects

1. a literal finite pure-clock exact-response cycle, and
2. a pure pair whose insiders refuse to leave while an outsider strictly
   prefers to join,

be strengthened by exact finite reward inequalities into a certificate that

\[
  \operatorname{Expl}_r(\sigma)\ge \gamma>0
  \qquad\text{for every behavioral profile }\sigma?
  \tag{1.1}
\]

The answer is negative for the local constraints themselves, even after adding
the standard residual-hard, full-normal-core, and no-stationary-exact-Nash
screens.

## 2. A finite rational constraint package

For a nonempty coalition \(K\subseteq\operatorname{Fin}4\), let \(x^K\) be
the pure-clock profile in which the members of \(K\) Quit at date zero and all
other players play Never.  Its payoff is \(r(K)\).  When a player toggles at
date zero and at least one other sure quitter remains, all later behavior is
screened.  Therefore its unrestricted behavioral response comparison is the
finite comparison

\[
  \begin{array}{ll}
  i\in K:& r_i(K)\quad\hbox{versus}\quad r_i(K\setminus\{i\}),\\[1mm]
  i\notin K:& r_i(K)\quad\hbox{versus}\quad r_i(K\cup\{i\}).
  \end{array}
  \tag{2.1}
\]

For a singleton owner, delaying the unique quit reproduces the singleton
reward and Never produces zero, so its cap is
\(\max\{r_i(\{i\}),0\}\).  Thus caps, debts, best-response signs, and a
deterministic max-debt response map on date-zero coalition profiles are all
given by finitely many rational linear inequalities.

Consider the following exact finite package \(C_{\rm local}(r,\delta)\):

* nonempty coalitions \(K_0,\ldots,K_{L-1}\) and movers
  \(i_0,\ldots,i_{L-1}\) are supplied, with indices read modulo \(L\);
* \(K_{k+1}=K_k\triangle\{i_k\}\), and the toggle preserves a nonempty
  quitting coalition;
* the toggle is an unrestricted exact best response at \(x^{K_k}\);
* \(i_k\) has maximum debt at \(x^{K_k}\), its gain is at least
  \(\delta>0\), and its target debt is zero;
* one displayed pair \(P\) has no profitable insider-leave toggle and has a
  strictly profitable outsider-join toggle.

Every item is a finite rational equality or inequality in the reward table.
One may further conjoin any finite reward-algebra screens such as residual-hard
membership and full normal-core membership.

This is a faithful finite formulation of the response-cycle and strategic-pair
obstructions.  It deliberately makes no claim that horizontal response edges
form one Nash--Bellman chronology.

## 3. Exact regression: the Solan--Vieille boundary table

Use `SolanVieilleBoundary.boundaryReward`.  The four relevant reward rows are

\[
\begin{array}{c|c}
K&r(K)\\ \hline
\{2\}&(0,0,1,4)\\
\{0,2\}&(1,1,1,0)\\
\{0,2,3\}&(0,0,0,1)\\
\{2,3\}&(1,1,1,1).
\end{array}
\tag{3.1}
\]

The date-zero coalition profiles form the literal cycle

\[
 \{2\}\xrightarrow{0}\{0,2\}
 \xrightarrow{3}\{0,2,3\}
 \xrightarrow{0}\{2,3\}
 \xrightarrow{3}\{2\}.
 \tag{3.2}
\]

Direct use of (2.1) gives

\[
\begin{array}{c|c|c|c}
K&d(x^K)&D(x^K)&\text{selected mover gain}\\ \hline
\{2\}&(1,1,0,0)&2&1\\
\{0,2\}&(0,0,0,1)&1&1\\
\{0,2,3\}&(1,0,1,0)&2&1\\
\{2,3\}&(0,0,3,3)&6&3.
\end{array}
\tag{3.3}
\]

Each selected mover is a maximum-debt player, each move is an exact complete
behavioral best response, and each target has zero mover debt.  A fixed player
tie order can select exactly (3.2).

The pair \(P=\{0,2\}\) also realizes the strategic-pair obstruction.  Neither
insider gains by leaving.  Outsider \(1\) loses by joining, while outsider \(3\)
strictly gains:

\[
 r_3(\{0,2,3\})-r_3(\{0,2\})=1.
 \tag{3.4}
\]

After division of every reward by \(4\), this is a normalized rational table.
The cycle remains exact, with uniform gain floor \(\delta=1/4\), and the strict
pair-join gain is \(1/4\).

## 4. Yet the table has an exact unrestricted equilibrium

The regression is stronger than a local hand calculation.  The repository
checks all of the following for the same unscaled table:

* `periodTwo_residualHardClass`;
* `periodTwo_residualHard_fullCore_nonstationary_but_uniform`, which packages
  residual-hard membership, full normal core, absence of every exact
  stationary terminal Nash profile, and existence of a uniform-equilibrium
  payoff;
* `periodTwoProfile_isExactTerminalNash`, against every behavioral deviation;
* `periodTwoProfile_terminalExploitability_eq_zero`;
* `periodTwo_terminalExploitabilityInf_eq_zero`; and
* `periodTwo_isUniformEquilibriumPayoff`.

The declarations are in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`
and
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`.
The reward rows are in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`.

Positive scaling preserves exact best-response signs, zero exploitability,
and the uniform-equilibrium conclusion.  Hence the normalized rational table
simultaneously satisfies \(C_{\rm local}(r,1/4)\) and has

\[
  \eta(r)=\inf_\sigma\operatorname{Expl}_r(\sigma)=0.
  \tag{4.1}
\]

Therefore none of the following finite screens, separately or together, is a
positive-gap certificate:

* a max-debt pure-clock response cycle with a fixed gain floor;
* a strategic pair with insider refusal and strict outsider joining;
* residual-hard membership;
* full normal core; or
* absence of stationary exact terminal Nash profiles.

This does **not** refute the source-attached positive-minimum pair question:
the regression has \(D_*=0\), so it has no positive-minimum ancestry to
retain.  It proves instead that positive global minimality and its causal
source passport are the essential extra data; they cannot be replaced by the
displayed finite reward signs.

The cycle does not contradict the equilibrium because it explores one finite
horizontal family of alternative profiles.  The exact equilibrium is a
different, genuinely chronological period-two profile.

## 5. Exact comparison with the escape-aware hierarchy

Let \(r\) be any normalized rational Fin4 reward code and let
\(\epsilon>0\) be rational.  The checked exact-scale resolver terminates with
one of two finite proof objects.

### Upper object

`finFourExactScaleStep_upper_sound` decodes an actual finite-clock behavioral
profile \(\sigma\) satisfying

\[
 \operatorname{Expl}_r(\sigma)<\frac{3\epsilon}{4},
 \tag{5.1}
\]

where exploitability still takes the supremum over the unrestricted complete
behavioral deviation class.

### Lower object

`FinFourExactScaleCertificate.lower_verifies_infimum_sound` says that an
independently accepted lower tree proves

\[
 \frac{\epsilon}{4}\le \eta(r).
 \tag{5.2}
\]

`FinFourExactScaleCertificate.lower_verifies_terminalGap` then supplies the
literal terminal gap \(\epsilon/8\).  Its proof uses only the normalized table,
the proof-free tree, and its Boolean verifier; it does not trust the search
that generated the tree.

The fixed-table completeness theorem
`exists_finFourFixedTableCounterexampleStep_of_infimum_pos` proves

\[
 \eta(r)>0
 \quad\Longrightarrow\quad
 \text{some finite fixed-table stage emits a verified lower certificate}.
 \tag{5.3}
\]

Conversely, when \(\eta(r)=0\),
`exists_finFourExactScaleStep_upper_profile_of_infimum_eq_zero` supplies an
upper finite-clock profile at every positive rational scale, and
`quittingGame_exists_uniformEquilibriumPayoff_of_finFourExactScale_infimum_eq_zero`
selects one fixed uniform-equilibrium payoff.

Thus a mathematically sufficient finite package is

\[
 C_{\rm local}(r,\delta)
 \quad+\quad
 \text{one independently verified exact-scale lower tree}.
 \tag{5.4}
\]

But all global soundness in (5.4) comes from the lower tree.  The local package
is only a candidate-region filter.

## 6. The precise missing condition

The finite local constraints do not inspect profiles outside their displayed
clock alphabet.  What they fail to exclude is exactly the escape alternative

\[
 \forall n\ge1\;\exists\text{ a finite-clock behavioral profile }\sigma_n:
 \operatorname{Expl}_r(\sigma_n)<\frac{3}{4}\,2^{-n}.
 \tag{6.1}
\]

For normalized rational tables, (6.1) is equivalent to \(\eta(r)=0\).
The forward implication follows immediately from nonnegativity of
exploitability and taking the infimum.  The reverse implication is the checked
finite-clock upper-profile theorem.  Any fixed positive infimum instead
eventually forces a lower event.

Accordingly, the obstruction is not an unknown finite-dimensional inequality
inside the response cycle.  It is uniform separation from **all** compatible
finite-clock escape profiles, equivalently

\[
 \exists\gamma>0\;\forall\sigma\quad
 \operatorname{Expl}_r(\sigma)\ge\gamma.
 \tag{6.2}
\]

At the semantic level, (6.1) or its negation is an infinite statement and is
invisible to any fixed list of coalition-response signs.  At the certificate
level, however, (6.2) is not inherently non-finitely certifiable: if it is
true for a rational table, the exact hierarchy compresses it into one finite
verified lower tree.

This distinction is the exact negative-search boundary:

* cycle and pair constraints can cheaply enumerate promising rational tables;
* upper witnesses must be allowed to escape every displayed local clock
  family;
* only a verified lower tree certifies a counterexample; and
* nontermination or failure to find an upper profile proves nothing.

## 7. Terminal conclusion

The pure-clock response cycle and strategic-pair obstruction do not force a
positive all-behavior gap, even under the strongest nearby finite algebraic
screens presently available.  The Solan--Vieille boundary table is an exact
regression: it satisfies them and nevertheless has a checked exact period-two
behavioral equilibrium.

The negative route therefore has a clean architecture but no counterexample:

\[
 \boxed{
 \text{finite local filter}
 \;\longrightarrow\;
 \text{fixed-table exact escape-aware search}
 \;\longrightarrow\;
 \text{independently verified lower tree or an upper witness}.}
 \tag{7.1}
\]

Any successful rational counterexample table will be found and finitely
certified by the existing fixed-table hierarchy.  What remains is candidate
generation or a theorem deriving a lower tree from genuinely global game
structure; the current response-cycle and pair passports do neither.
