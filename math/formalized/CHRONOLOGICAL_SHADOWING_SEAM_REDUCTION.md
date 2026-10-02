# Summable artificial seams compile chronological shadowing

Authors: `CODEX_CEDAR`

Independent reviews:
[Gauss, repaired seam adapter](../feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_GAUSS__ROUND_2.md),
[Noether, repaired seam adapter](../feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER.md),
and
[Noether, semantic rigidity](../feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER__ROUND_2.md).

## Exact statement

Let `I` be a finite nonempty player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table. At every live date, player `i`
independently Quits with probability `p_i`; if the nonempty set `S` Quits,
play absorbs with reward `r(S)`, and otherwise the unique live state repeats.

For a product root `q=(p_i)_{i\in I}`, put

\[
 J(q)=\prod_{i\in I}(1-p_i),\qquad
 O_i(q)=\prod_{j\ne i}(1-p_j).
\]

A terminal semantic pair is an arbitrary pair `X=(u,b)` of payoff vectors.
Its prefix `F_q(X)` has prescribed coordinate equal to the expected payoff
from playing `q` once and using `u` after all Continue. Its cap coordinate for
player `i` is

\[
 F_q(X).2_i=\max\{Q_i(q),\ C_i(q)+O_i(q)b_i\},           \tag{1}
\]

where `Q_i(q)` is the payoff when `i` is forced to Quit at the displayed
row, and `C_i(q)` is the terminal contribution when `i` is forced to
Continue and at least one opponent Quits. Define the debt of `X` by

\[
 d_i(X)=b_i-u_i.
\]

No semantic pair below is assumed to be realized by a behavioral profile
unless explicitly called actual.

### Theorem A: summable-seam certificate reduction

Fix `eta>0`. For each `k in Nat`, let `N_k>=1`, let

\[
 q_{k,t}\quad(0\le t<N_k)
\]

be product roots, and let

\[
 X_{k,t}=(u_{k,t},b_{k,t})\quad(0\le t\le N_k)
\]

be arbitrary candidate pairs. Assume:

1. Every internal block row is an exact candidate Bellman row:

   \[
   X_{k,t}=F_{q_{k,t}}(X_{k,t+1}).                     \tag{2}
   \]

2. Candidate debts are coordinatewise nonnegative. There are finite `C,D`
   such that, for all `k,t,i`,

   \[
   |u_{k,t,i}|\le C,\qquad |b_{k,t,i}-u_{k,t,i}|\le D. \tag{3}
   \]

3. Initial candidate debt is small:

   \[
   b_{0,0,i}-u_{0,0,i}\le\eta\quad\text{for every }i. \tag{4}
   \]

4. At seam `k`, define

   \[
   A_{k,i}=|u_{k,N_k,i}-u_{k+1,0,i}|,
   \quad
   B_{k,i}=|b_{k,N_k,i}-b_{k+1,0,i}|.                  \tag{5}
   \]

   For every player,

   \[
   \sum_k A_{k,i}\le\eta,
   \qquad
   \sum_k(A_{k,i}+B_{k,i})\le\eta.                    \tag{6}
   \]

5. Concatenate the literal roots in increasing `(k,t)` order. On every
   suffix, joint survival tends to zero and survival after deleting any one
   player's clock tends to zero.

Then the concatenated literal roots and the inherited candidate annotations
form a `QuittingChronologicalDebtShadowingCertificate r eta`.

In item 5 it suffices, when `|I|>=2`, that two distinct fixed labels have
divergent cumulative marginal Quit hazards. This is the already established
two-label reduction recorded in
[`PERSISTENT_DELETED_CLOCK_TWO_LABEL_REDUCTION.md`](../formalized/PERSISTENT_DELETED_CLOCK_TWO_LABEL_REDUCTION.md).

### Theorem B: bounded-chain semantic rigidity

Under items 1, 2, and 5 of Theorem A, let `(U_0,B_0)` be the actual terminal
prescribed-payoff/all-behavior-cap pair of the infinite concatenated root
profile. Then, for every player `i`,

\[
 |U_0(i)-u_{0,0,i}|\le\sum_k A_{k,i},                  \tag{7}
\]

\[
 |B_0(i)-b_{0,0,i}|\le\sum_k B_{k,i},                  \tag{8}
\]

and hence

\[
 |(B_0-U_0)(i)-(b_{0,0}-u_{0,0})(i)|
 \le\sum_k(A_{k,i}+B_{k,i}).                          \tag{9}
\]

In particular, a bounded zero-seam chain is exactly the actual terminal
semantic pair of its infinite root profile.

If `Delta>0` is a lower bound on total actual terminal debt of every
behavioral profile,

\[
 \Delta\le\sum_i(B-U)(i),                              \tag{10}
\]

then every chain satisfying items 1, 2, and 5 obeys the unavoidable seam
toll

\[
 \Delta\le
 \sum_i\left[(b_{0,0}-u_{0,0})(i)
       +\sum_k(A_{k,i}+B_{k,i})\right].                \tag{11}
\]

Thus the full hypotheses of Theorem A imply

\[
 \Delta\le 2|I|\eta.                                  \tag{12}
\]

Consequently, if Theorem A can be instantiated for every positive `eta`, the
checked chronological consumer produces one fixed uniform-equilibrium payoff.

## Conjecture-facing change

The named live arrow is

```text
VANISHING-DEBT-ATOM-ACCESS -> CHRONOLOGICAL-DEBT-SHADOWING.
```

The open conditioned-reprojection formulation asks for source-matched finite
packets controlling prescribed defects, direct-debt defects, joint survival,
and every deleted survival on all suffixes. Theorem A strictly narrows its
non-survival part: retain the literal root words, make the inside of every
candidate block exactly Bellman, and control only the countably many seam
coordinates by the two `l1` budgets (6). No pair need be an executable
semantic state.

Theorem B removes a tempting shortcut. Bounded artificial annotations with
vanishing literal clocks cannot hide a nonsmall endpoint behind zero seams:
the semantic discrepancy is at most the actual seam toll. Under a positive
terminal-debt gap, the toll has the quantitative lower bound (11).

The actual producer remains open. The checked atom/reset source does not yet
construct bounded artificial Bellman blocks with summable seams, small first
debt, and two persistent labels on one reached chronology.

## Definitions and assumptions

The root sequence is deterministic conditional on the sole public live
history. At each root the players' randomizations are independent. Dates need
not be probabilistically independent beyond the product of the prescribed
conditional Continue masses along that live history. Simultaneous Quit is
observed as one terminal coalition, including all ties and probability-one
Quit roots. A strategy may assign positive mass to Never.

The cap coordinate is the supremum over every unilateral behavioral strategy
of the selected player against the fixed opponents' complete behavioral law.
It is not a one-shot or stationary-deviation envelope, and the supremum need
not be attained. Formula (1) is valid because, after the displayed row, only
the all-opponents-Continue event retains the deviator's future agency.

The theorems themselves produce terminal chronological certificates. The
power of an unrestricted behavioral deviator enters through the cap
coordinate and through the checked certificate consumer; no purification or
bounded-controller completeness assertion is used here. The fixed uniform
target in the final consequence is selected by the existing terminal-Nash
compactness theorem, not separately for each horizon.

## Source correspondence

The exact prefix and semantic-debt definitions are
`quittingTerminalSemanticPrefix` and `quittingTerminalSemanticDebt`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`). The generated
max-affine secant is
`exists_quittingTerminalSemanticPrefix_secant`, and the target structure and
consumer are `QuittingChronologicalDebtShadowingCertificate` and
`quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`).

`QuittingChronologicalDebtData.exactOfRoots`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ExactChronologicalData.lean`)
gives zero defects for any literal root schedule, but its candidate debt is
the schedule's actual terminal exploitability. It does not give a small-debt
annotation.

The current actual source declarations inspected were
`exists_executable_positiveIncidence_normalizedReprojectionGerm` and
`exists_sameProfile_finiteWindow_defectPacket`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionWindow.lean`),
`QuittingReprojectionDiffuseWindowPacket.eventually_matchedChronology`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionDiffuseClockBridge.lean`),
and `resetFace_globalMinimum_or_surfaceTension_reprojectionCostate`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetFaceReprojection.lean`).
They provide frozen or same-profile finite-window data, not a summably
source-matched sequence of block endpoints.

No paper result is used.

## Proof

### One-root seam estimates

For arbitrary successor pairs `X=(u,b)` and `Y=(u',b')`, only the
all-Continue event reads the prescribed successor, so

\[
 |F_q(X).1_i-F_q(Y).1_i|=J(q)|u_i-u'_i|.               \tag{13}
\]

By (1), the cap is the scalar function

\[
 H_i(z)=\max\{Q_i,C_i+O_i z\}.
\]

Because `O_i>=0`, this function is globally `O_i`-Lipschitz, including a
switch of the maximizing branch. Hence

\[
 |F_q(X).2_i-F_q(Y).2_i|\le O_i(q)|b_i-b'_i|.          \tag{14}
\]

Subtracting prescribed payoff from cap and using the triangle inequality
gives

\[
 |d_i(F_q(X))-d_i(F_q(Y))|
 \le J(q)|u_i-u'_i|+O_i(q)|b_i-b'_i|.                  \tag{15}
\]

### Proof of Theorem A

Inside each block, (2) makes both the candidate prescribed defect and the
candidate direct-debt defect zero. At seam `k`, the annotated last row was
computed from `X_{k,N_k}`, whereas the globally concatenated successor is
`X_{k+1,0}`. Equations (13)--(15) give

\[
 |P_{k,i}|\le A_{k,i},\qquad
 |E_{k,i}|\le A_{k,i}+B_{k,i}.                         \tag{16}
\]

Every finite calendar interval contains only a subset of the seams, so (6)
gives absolute prescribed discrepancy at most `eta`.

At each global row, apply the generated-secant theorem to the arbitrary
candidate successor and the actual semantic pair of the literal next suffix.
This produces `s_{t,i}` satisfying

\[
 0\le s_{t,i}\le O_i(q_t)\le1                          \tag{17}
\]

and the exact cap-error recursion required by the certificate. Every secant
survival weight `w_{t,i}` therefore lies in `[0,1]`. For every finite suffix,

\[
 -\sum_t w_{t,i}E_{t,i}
 \le\sum_k|E_{k,i}|
 \le\eta.                                             \tag{18}
\]

This is stronger than the certificate's eventual `eta+slack` clause. Items
2--3 give nonnegative bounded candidate debt and small initial debt; item 5
gives both survival fields. These are all certificate fields.

### Proof of Theorem B

Let `(U_t,B_t)` be the actual terminal semantic pair of the literal suffix
beginning at date `t`. It satisfies

\[
 (U_t,B_t)=F_{q_t}(U_{t+1},B_{t+1}).                   \tag{19}
\]

Let `e^u_{t,i}` and `e^b_{t,i}` be the prescribed and cap residuals of the
candidate sequence. They vanish off seams, and at seam `k` their absolute
values are at most `A_{k,i}` and `B_{k,i}`. Subtracting (19) from the
candidate recursion and using (13)--(14) yields

\[
 |u_t(i)-U_t(i)|
 \le |e^u_{t,i}|+J(q_t)|u_{t+1}(i)-U_{t+1}(i)|,        \tag{20}
\]

\[
 |b_t(i)-B_t(i)|
 \le |e^b_{t,i}|+O_i(q_t)|b_{t+1}(i)-B_{t+1}(i)|.      \tag{21}
\]

Iterate to a finite terminal date. The boundary term in (20) is joint
survival times a uniformly bounded difference; the boundary term in (21) is
player-`i`-deleted survival times a uniformly bounded difference. Actual
payoffs and unrestricted caps are reward-bounded, and candidate caps are
bounded by (3). Item 5 makes both remainders tend to zero. Dropping the
earlier survival weights, all of which lie in `[0,1]`, proves (7)--(8), and
the triangle inequality proves (9).

Apply the assumed actual-carrier lower bound (10) to the literal concatenated
profile. Equation (9), coordinatewise candidate-debt nonnegativity, and
summation over players give (11). Under Theorem A, (4) and the second series
in (6) each contribute at most `eta` per player, proving (12).

## Boundary tests

- **Exact positive seam regression.** Take two players, the zero reward table,
  and at every displayed row let both players Quit surely. Then
  `J=O_0=O_1=0`, so `F_q(X)=(0,0)` for every donated pair `X`, and every
  joint and deleted survival product dies at its first row. For blocks of
  length one, set `X_(k,0)=(0,0)` and let both coordinates of the donated
  endpoint `X_(k,1)` equal the constant
  `a_k=eta/2^(k+3)`. Exact block recursion holds, candidate debt and initial
  debt are zero, and for each player `A_(k,i)=B_(k,i)=a_k`. Hence
  `sum_k A_(k,i)=eta/4` and
  `sum_k(A_(k,i)+B_(k,i))=eta/2`. Theorem A applies with genuinely nonzero
  donated endpoint seams, while the sure-absorption roots screen the actual
  defects completely.
- **Cap seams cannot be omitted.** At an all-Continue root, if both successor
  caps lie above the forced-Quit branch, the cap mismatch passes with
  coefficient one. Matching prescribed payoffs alone does not bound the
  direct-debt seam.
- **Semantic pair plus joint survival does not preserve a labelled clock.**
  In the three-player regression
  `QuittingCommonWitnessNoncompositionality.semanticPair_eq`,
  `jointSurvival_eq`, and `deletedSurvival_ne`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessNoncompositionality.lean`),
  only player `0` Quits with probability `1-s` in profile `P`, while only
  player `1` does so in profile `Q`. The table pays player `0` one on either
  singleton `{0}` or `{1}`, two on `{0,2}`, and zero otherwise; all other
  coordinates are zero. For `0<s<1`, both profiles have prescribed payoff
  `1-s` and cap `1` for player `0` (zero for the other players), and both have
  joint Continue mass `s`. After deleting player `0`, however, the one-row
  Continue masses are respectively `1` and `s`. Thus equal complete semantic
  pairs and joint survival do not determine the labelled deleted clock.
  The bundled statement is
  `exists_terminalSemantic_commonWitness_noncompositionality` in the same
  file.
- **`exactOfRoots` does not solve initial debt.** It makes both defect series
  zero but copies the literal profile's actual exploitability into candidate
  debt. A two-player table with every nonempty terminal reward `(1,1)` and an
  all-Continue root sequence has zero Bellman defects but actual initial debt
  one for each player.
- **Boundedness is essential to rigidity.** Candidate endpoints growing like
  the reciprocal of the relevant survival can leave a nonzero terminal
  remainder in (20) or (21).
- **Deleted survival is essential.** Joint survival alone does not kill a
  best-response-cap boundary term after deleting the deviating player's own
  clock.

## Adapter and consumer

For a supplied literal chronology, Theorem A converts exact artificial
Bellman blocks and two scalar seam budgets into every non-survival field of
`QuittingChronologicalDebtShadowingCertificate`. The checked two-label
reduction converts two divergent fixed marginal hazards into all its survival
fields.

The downstream consumer is
`quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`.
Its intermediate theorem `QuittingChronologicalDebtShadowingCertificate.isAsymptoticNash`
covers every unilateral behavioral deviation and gives terminal error
`4*eta`.

This packet qualifies as a strict reduction of the named open producer, not
as an actual-data solution. No checked declaration currently maps arbitrary
vanishing-debt atom access to the hypotheses above. In particular,
independently selected frozen packets are not a reached root chronology, and
same-profile finite windows do not match a moving endpoint to the next source
at a summable rate.

## Lean handoff

The narrowest useful formal targets are:

1. a one-root theorem giving the three seam estimates for arbitrary
   `QuittingTerminalSemanticPair`s;
2. a block-flattening certificate constructor from (2)--(6), reusing
   `exists_quittingTerminalSemanticPrefix_secant`;
3. a semantic-rigidity theorem obtained by iterating the two Lipschitz
   recursions and killing their bounded terminal remainders with joint and
   deleted survival.

Likely dependencies are
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`,
`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`,
and `UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`.

Finite regression checks should include the zero-table sure-absorption
construction above, a max-branch switch, and an all-Continue seam with
unsuppressed cap displacement. The implementation should not encode
candidate carrier membership, actual initial Nash debt, or the desired
source-matching producer as a structure hypothesis.

## Scope and nonclaims

This packet does not construct a chronology from vanishing-debt atom access,
prove conditioned packet reprojection, select summable seams, retain two
labels through moving-source reprojection, or
prove the finite-quitting conjecture. It does not claim that artificial
candidate pairs are executable semantic pairs. It does not reduce arbitrary
finite stochastic games to quitting games. It makes no Lean-check claim for
the new statements and uses no paper theorem.
