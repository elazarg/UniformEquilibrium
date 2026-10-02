# Positive debt does not close the attained terminal-semantic image

Authors: `CODEX_FERMAT` (counterexample supplied by the user; source audit and
packaging by the conference coordinator)

Independent reviews:
[`CODEX_RAMSEY`](../feedback/CODEX_FERMAT__POSITIVE_DEBT_SEMANTIC_NONATTAINMENT__BY_CODEX_RAMSEY.md),
[`CODEX_MINER`](../feedback/CODEX_FERMAT__POSITIVE_DEBT_SEMANTIC_NONATTAINMENT__BY_CODEX_MINER.md)

## Exact statement

For a finite quitting reward table `r` and an actual behavioral profile
`sigma`, write

\[
 U_i(\sigma)=\operatorname{Payoff}_i(\sigma),
 \qquad
 B_i(\sigma)=\sup_{\tau_i}
   \operatorname{Payoff}_i(\sigma[i\leftarrow\tau_i]),
\]

where the supremum is over every unilateral behavioral strategy of player
`i`.  Define

\[
 \operatorname{Sem}(\sigma)=(U(\sigma),B(\sigma)),\qquad
 D(U,B)=\sum_i(B_i-U_i),
\]

and let

\[
 \mathcal S_r=\{\operatorname{Sem}(\sigma):
   \sigma\text{ is an actual behavioral profile}\}.
\]

There is a rational two-player reward table for which all of the following
hold.

1. There are actual profiles `sigma_n`, indexed by integers `n>=1`, with

   \[
   \operatorname{Sem}(\sigma_n)
      =((-1,0),(0,1/n)),\qquad
   D(\operatorname{Sem}(\sigma_n))=1+1/n.
   \]

2. These pairs converge to

   \[
   z=((-1,0),(0,0)),\qquad D(z)=1,
   \]

   but no actual behavioral profile realizes `z`.  Consequently

   \[
   \mathcal S_r\cap\{(U,B):D(U,B)\ge1\}
   \]

   is not closed.

3. The whole relevant face is exactly

   \[
   \mathcal S_r\cap\{(U,B):U_c=-1\}
    =\{((-1,0),(0,\alpha)):0<\alpha\le1\}.
   \]

4. Two players are cardinal-minimal: for every one-player quitting table,
   the attained terminal-semantic set is a closed line segment.

Crucial boundary: the example's global minimum semantic debt is

\[
D_*=0,
\]

witnessed by all-Never play.  The result does **not** refute realization or
compactification on a globally minimal fiber satisfying `D=D_*>0`.

## Conjecture-facing change

The compact minimum-debt route works with the closure of actual terminal
semantic pairs.  A natural shortcut was to infer that a carrier limit becomes
behaviorally attainable as soon as its total debt is positive.  This packet
rules out exactly that inference:

```text
z_n actual, z_n -> z, D(z)>0  does not imply  z actual.
```

Thus pointwise positive debt cannot by itself prevent temporal stopping mass
from escaping to later and later dates.  Any attainment theorem used in the
positive-minimum program must genuinely use additional data such as global
minimality `D(z)=D_*>0`, source chronology, punishment structure, or another
compactness modulus.

This is a route-elimination result only.  It neither proves nor disproves the
finite-quitting uniform-equilibrium conjecture, and it supplies no terminal
exploitability gap.

## Definitions and assumptions

There are two players, called `c` (the clock) and `a` (the atom tester).  Payoff
coordinates are ordered `(c,a)`.  The rewards of the three nonempty quitting
coalitions are

\[
 r(\{c\})=(-1,0),\qquad
 r(\{a\})=(0,0),\qquad
 r(\{c,a\})=(0,1).                       \tag{1}
\]

If nobody ever quits, the terminal payoff is zero.  At each live date the
players observe the common live history and independently sample their
behavioral actions.  No public or correlated randomization is added.
Strategies in both the attained set and the nonattainment claim are arbitrary
behavioral strategies: they need not be stationary, Markov, finite-memory, or
proper.  A unilateral deviator replaces its complete behavioral strategy.

For `n>=1`, player `a` plays Never and player `c` uses the live-date hazards

\[
 q_c^{(n)}(t)=
 \begin{cases}
  1/(n-t),&0\le t<n,\\
  0,&t\ge n.
 \end{cases}                                      \tag{2}
\]

The hazard at `t=n-1` is one, so this clock is proper.

## Source correspondence

The existing checked semantic infrastructure is:

- `quittingContinuationBestResponseValue_eq_sSup_`
  `pureTimeDeviationPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/`
  `TerminalSemanticPositiveSlopeRectangle.lean`, which identifies the full
  behavioral best-response cap with the supremum of deterministic finite
  quit-time and Never values;
- `quittingBehaviorStoppingLaw` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`, which records
  an arbitrary live-spine behavioral strategy as a probability law on
  `Option Nat`; and
- `quittingStoppingLawBehaviorStrategy` and
  `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
  `UniformEquilibrium/Quitting/Terminal/`
  `StrategicallyPrecompactWatchdogProperBoundary.lean`, which realize every
  complete stopping law by an actual behavioral strategy.

The exact two-player nonclosed face proved here is not present in those
files.  It is also distinct from the following nearby regressions.

- `TerminalSemanticFixedTableDiffuseIncidenceRegression.lean` and
  `TerminalSemanticFixedTableCapDefectRegression.lean` use a three-player
  one-row family to separate persistent incidence from vanishing local Nash
  defect.  They do not prove nonclosedness or identify an unattained semantic
  pair.
- `StationarilyGeneratedCompactnessObstruction.lean` gives a one-player
  discontinuity of terminal payoff and exact Nash under coordinatewise root
  convergence.  Its limiting profile failure is not nonclosedness of the
  attained semantic-pair image on a positive-debt slice.
- The pure-payoff singularity in
  `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` and the paid
  first-disagreement conditioning regression use related diffuse clocks but
  refute different continuity or survival claims.

No paper theorem is being translated.  The counterexample is a new exact
boundary statement about the repository's unrestricted behavioral terminal
semantics.

## Proof

### 1. The diffuse clock

Let `T_c` be the complete stopping time induced by (2).  For `0<=t<n`, its
survival probability telescopes:

\[
 \Pr(T_c\ge t)
 =\prod_{u=0}^{t-1}\left(1-\frac1{n-u}\right)
 =\frac{n-t}{n}.
\]

It follows that

\[
 \Pr(T_c=t)=\Pr(T_c\ge t)q_c^{(n)}(t)=\frac1n
 \quad(0\le t<n),                                \tag{3}
\]

and `T_c` has no mass at Never.

Under prescribed play the terminal coalition is `{c}` almost surely, hence

\[
 U(\sigma_n)=(-1,0).                              \tag{4}
\]

Every possible terminal reward of `c` is at most zero, and by deviating to
Never player `c` obtains zero.  Therefore its unrestricted cap is

\[
 B_c(\sigma_n)=0.                                 \tag{5}
\]

If player `a` deviates to Quit at deterministic date `t`, it receives one
exactly when `T_c=t`: an earlier clock quit produces `{c}`, a later clock quit
is preempted by `{a}`, and a same-date quit produces `{c,a}`.  The deviation
value is therefore `1/n` for `0<=t<n` and zero otherwise.  Never also gives
zero.  Behavioral pure-time extremality now covers every randomized and
history-dependent unilateral deviation, giving

\[
 B_a(\sigma_n)=\sup_t\Pr(T_c=t)=1/n.              \tag{6}
\]

Equations (4)--(6) prove the displayed semantic pair and debt.  Their limit is
`z=((-1,0),(0,0))`, so `z` belongs to the closure of the attained image and
has debt one.

### 2. The limit is not behaviorally attained

Suppose an arbitrary behavioral profile `sigma` realizes `z`.  In table (1),
player `c` earns `-1` exactly on terminal coalition `{c}` and earns zero on
`{a}`, `{c,a}`, and Never.  Hence

\[
 U_c(\sigma)
   =-\Pr_\sigma(\text{terminal coalition is }\{c\}). \tag{7}
\]

The required equality `U_c=-1` forces `{c}` to occur almost surely.  In
particular the live-spine stopping law of `c` is proper: it is a probability
law `mu` on the countable set `Nat`.  Since

\[
 \sum_{t\in\mathbb N}\mu(t)=1,
\]

some finite date `t` satisfies `mu(t)>0`.

Now replace only player `a` by the deterministic quit-at-`t` behavioral
strategy.  Up to that date it follows the same all-Continue live history, so
the live-spine hazards of the unchanged player `c` retain the law `mu`.
Product behavioral sampling makes the deviator's terminal payoff exactly

\[
 \Pr(T_c=t)=\mu(t)>0.                              \tag{8}
\]

Thus `B_a(sigma)>0`, contradicting the required cap coordinate `B_a=0`.
This proves nonattainment for all behavioral profiles, not only for the
displayed clock family.

Because every approximating pair lies in `{D>=1}`, while its limit `z` is not
in the attained set, `\mathcal S_r\cap\{D\ge1\}` is not closed.

### 3. Exact characterization of the face

Let an arbitrary actual profile satisfy `U_c=-1`.  Equation (7) again forces
terminal `{c}` almost surely.  Therefore `U_a=0`.  All terminal rewards of `c`
are nonpositive and Never guarantees zero, so `B_c=0`.  If `mu` is `c`'s
proper stopping law, the same pure-time calculation gives

\[
 B_a=\sup_{t\in\mathbb N}\mu(t)>0.                \tag{9}
\]

The strict positivity follows because a countably supported probability law
cannot have every atom zero.

Conversely, fix any `alpha in (0,1]`.  Put one atom of mass `alpha` at one
finite date.  Choose a positive integer `k` large enough that
`(1-alpha)/k <= alpha`, and split the remaining mass equally among `k`
additional finite dates.  This is a proper finite stopping law whose largest
atom is exactly `alpha`.  Realize it as player `c`'s behavioral stopping law
and prescribe Never for `a`.  The calculations above give

\[
 (U,B)=((-1,0),(0,\alpha)).
\]

This proves both inclusions in the exact face formula.

### 4. One-player minimality

Let a one-player quitting game have singleton reward `rho`.  Every behavioral
strategy is summarized, for terminal semantics, by its eventual quitting
probability `p in [0,1]`.  Its prescribed payoff is

\[
 U=p\rho.
\]

The player can Quit at any fixed finite date for payoff `rho`, or play Never
for payoff zero.  Pure-time extremality therefore gives the profile-independent
cap

\[
 B=\max\{\rho,0\}.                                \tag{10}
\]

Every `p in [0,1]` is realized, for example by quitting at date zero with
probability `p` and thereafter playing Never.  Thus the attained semantic set
is the continuous image

\[
 \{(p\rho,\max\{\rho,0\}):0\le p\le1\},
\]

a closed line segment.  Hence no one-player example can exhibit the asserted
nonclosedness.

## Boundary tests

1. **First diffuse clocks.**  At `n=1`, player `c` surely quits at date zero,
   so `B_a=1`.  At `n=2`, its two stopping atoms are each `1/2`, so
   `B_a=1/2`.  These agree with (6), including the sure-collision endpoint.
2. **Non-reciprocal face values.**  The value `alpha=2/3` is realized by the
   two-atom clock law `(2/3,1/3)`.  The exact face is not limited to reciprocal
   values arising from the uniform approximating sequence.
3. **Improper candidate profiles.**  A positive Never atom for `c` is
   incompatible with `U_c=-1`, since it prevents terminal `{c}` from having
   probability one.  Allowing improper behavioral profiles therefore does
   not open a loophole in the nonattainment proof.
4. **Global minimum.**  Under all-Never play every prescribed payoff and every
   unilateral cap is zero for table (1).  Hence its semantic pair is diagonal
   zero and `D_*=0`.  This directly falsifies any attempt to read the example
   as a positive-global-minimum counterexample.

## Adapter and consumer

The actual-data adapter is explicit: the rational reward table (1), the
behavioral hazards (2), and the all-Never strategy of `a` construct every
approximating semantic pair.  Arbitrary complete stopping laws provide the
converse realization needed for the exact face.

The result is itself the consumer of the proposed compactness shortcut.  It
shows that the map from actual behavioral profiles to terminal semantic pairs
has a nonclosed image even after intersecting with one fixed positive-debt
half-space.  Therefore an argument that selects a positive-debt carrier limit
cannot decode it to an actual profile from debt positivity alone.

No positive theorem downstream of `PositiveMinimumSemanticDebt.lean` is
invalidated: those results work in the compact carrier and use global minimum
debt.  The packet only prevents adding an unjustified carrier-to-profile
attainment step without stronger hypotheses.

## Lean handoff

Use `Bool` or `Fin 2` for the two-player type and define a namespace-local
rational reward table with the three rows in (1).  A narrow implementation can
introduce declarations of the following shapes.

```text
positiveDebtNonattainment_pair (n : Nat) :
  Sem (sigma (n+1)) = ((-1,0),(0,1/(n+1)))

positiveDebtNonattainment_tendsto :
  Tendsto (fun n => Sem (sigma (n+1))) atTop (nhds z)

positiveDebtNonattainment_not_realized :
  not exists sigma, Sem sigma = z

positiveDebtNonattainment_face :
  attainedSet r intersect {pair | pair.1 c = -1}
    = {((-1,0),(0,alpha)) | 0 < alpha and alpha <= 1}
```

Recommended dependencies are:

- `BehaviorPureTimeExtremality.lean` or the wrapper
  `quittingContinuationBestResponseValue_eq_sSup_`
  `pureTimeDeviationPayoff` for unrestricted caps;
- `BehaviorStoppingLaw.lean` for the intrinsic stopping law of an arbitrary
  candidate profile;
- `StrategicallyPrecompactWatchdogProperBoundary.lean` for realization of the
  converse finite laws; and
- the existing terminal semantic-pair, debt-sum, and carrier definitions.

For nonattainment, extract a positive `some t` atom from a PMF on
`Option Nat` whose `none` atom is zero; do not replace the arbitrary candidate
profile by a stationary or explicitly parameterized subclass.  The one-player
closed-image theorem is independent of the core counterexample and can be
formalized separately if it would enlarge the dependency footprint.

## Scope and nonclaims

- This is ordinary mathematics awaiting Lean formalization; the packet itself
  carries no `L`, `A`, or `C` seal.
- The nonattainment quantifier covers all unilateral behavioral strategies,
  but the theorem is a topological no-go, not a terminal-gap counterexample.
- The table has a uniform equilibrium and has global minimum debt `D_*=0`.
- The result does not address the open case `D=D_*>0`.
- It does not show that the compact terminal-semantic carrier is noncompact;
  the failure is closedness of the subset realized by literal profiles.
- It does not invalidate compactness arguments which retain complete stopping
  laws, literal source chronology, or a genuine global-minimum hypothesis.

## Checked Lean realization

Formalization used the reviewed export at SHA-256
`e7e2bb213d9e8b0046ae74adc2d7d4c46ed16ce437829730d729609d9a35fc0c`.
The frozen Lean module has SHA-256
`7ae37c336401807362d3b53f40121b6165fec6ca63f31c9a7a399b4d904d1b89`.

The packet is realized in
`UniformEquilibrium/Diagnostics/Quitting/`
`PositiveDebtTerminalSemanticNonattainment.lean`.  Its result-level
declaration inventory is:

- `PositiveDebtTerminalSemanticNonattainment.profile_semanticPair` and
  `approximatingPair_debtSum`, giving the exact executable pairs and their
  debts;
- `profile_semanticPair_tendsto_limitPair` and `limitPair_mem_carrier`, giving
  convergence to the positive-debt carrier point;
- `globalMinimumDebt_eq_zero`, recording the essential zero-global-minimum
  fence;
- `attainable_inter_clock_payoff_face`, identifying the entire attained open
  face;
- `limitPair_not_mem_attainable`, quantifying over arbitrary behavioral
  profiles;
- `limitPair_debtSum` and `attainable_inter_debt_ge_one_not_closed`, proving
  debt one at the missing endpoint and nonclosedness on the `D >= 1` slice;
  and
- `OnePlayerTerminalSemanticMinimality.attainable_eq_closed_segment` and
  `attainable_isClosed`, proving the one-player minimality statement.

The same module contains the explicit rational reward table, diffuse-clock
profiles, unrestricted best-response-cap calculations, complete-stopping-law
realizations, and face-characterization adapters used by these declarations.

Evidence seals:

- `M`: the exact construction, arbitrary-profile nonattainment argument, face
  characterization, and one-player minimality passed two independent audits;
- `L`: the declarations above are checked by Lean, both directly and as the
  named module;
- `A`: the approximating sequence consists of literal behavioral profiles,
  and the nonattainment proof extracts its profitable pure-time deviation from
  an arbitrary candidate profile's complete stopping law; and
- direct no-go `C`: `attainable_inter_debt_ge_one_not_closed` itself consumes
  and refutes the proposed positive-pointwise-debt attainment shortcut.  This
  is not a consumer for the globally minimal `D = D_* > 0` frontier.

The four displayed boundary tests remain audited mathematical examples rather
than separate Lean regression declarations.  The table has an executable
zero-debt pair, so the result neither supplies a terminal exploitability gap
nor proves or refutes the finite-quitting uniform-equilibrium conjecture.
