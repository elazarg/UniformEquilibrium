# Local periodic anchor obstructions

Authors: external derivation in `COMP_b.md` / `FACE_ENLARGE_FOLLOWUP.md`,
assembled by Codex Root

Independent reviews and falsification attempts:
[Codex Archimedes](../feedback/FACE_ENLARGE_FOLLOWUP__BY_CODEX_ARCHIMEDES.md),
[Codex Leibniz](../feedback/FACE_ENLARGE_FOLLOWUP__BY_CODEX_LEIBNIZ__FALSIFICATION.md),
and [Codex Aristotle](../feedback/COMP_B__BY_CODEX_ARISTOTLE.md)

## Exact statements

Let `I` be a nonempty finite player set and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table.  Infinite all-Continue play pays zero.
Write

\[
s_i:=r_i(\{i\}),
\qquad
M_{ij}:=r_i(\{j\})-r_i(\{i\}).
\tag{1}
\]

### Theorem A: minimum-tube Never barrier

Assume `|I|=n>=2`, fix a nonempty finite period `K`, and periodically repeat
independent product roots `x_0,...,x_{K-1}`.  Write

\[
q_{k,i}:=\Pr_{x_k}(i\text{ Quits}),
\quad
\beta_k:=\prod_i(1-q_{k,i}),
\quad
\beta_{k,-i}:=\prod_{j\ne i}(1-q_{k,j}).
\]

Let `u_k` be the actual infinite-periodic terminal payoff when phase `k` is
the initial phase.  Suppose `R>=0`, `eta>0`, and

\[
|r_i(S)|\le R \quad(S\ne\varnothing,i\in I),
\tag{2}
\]

\[
u_{k,i}\ge s_i+\eta\quad(k,i),
\tag{3}
\]

\[
m:=\max_{k,i}q_{k,i}
\le {\eta\over 2(n-1)(\eta+2R)},
\tag{4}
\]

and the period has positive absorption:

\[
\prod_{k<K}\beta_k<1.
\tag{5}
\]

Then the terminal exploitability of the periodic behavioral profile, against
all unilateral behavioral deviations, satisfies

\[
\boxed{
\max_i\bigl(B_i-U_i\bigr)\ge {\eta\over2n}.}
\tag{6}
\]

No separate deleted-player contraction hypothesis is required.

### Fin4 minimum-fiber corollary

In the maintained `Fin 4` positive-minimum hard residual, punishment
normality and compactness supply `delta>0` such that every minimum-fiber pair
`(u,b)` satisfies

\[
u_i-s_i\ge\delta\qquad(i\in\operatorname{Fin}4).
\tag{7}
\]

Choose a neighborhood of the prescribed minimum-fiber projection on which
the gap is at least `delta/2`.  Every positively absorbing periodic product
profile whose actual phase payoffs lie in that neighborhood and whose maximum
row hazard is at most

\[
{\delta/2\over 6(\delta/2+2R)}
\]

has terminal exploitability at least

\[
\boxed{\delta/16.}
\tag{8}
\]

The period length may vary between profiles.  Thus no vanishing-mesh periodic
chronology with actual values confined to the minimum tube can be a terminal
approximation.

### Theorem B: solo-anchor prescribed-closure obstruction

For every natural index `h`, let `K_h>=1`, let

\[
x^h_k\qquad(k\in\mathbb Z/K_h\mathbb Z)
\]

be product roots, and let `u^h_k in R^I` be cyclic payoff annotations.  Write

\[
q^h_{k,j}:=\Pr_{x^h_k}(j\text{ Quits}),
\]

\[
A_h:=\sum_{k<K_h}\sum_jq^h_{k,j}>0,
\qquad
Q_{h,j}:=\sum_{k<K_h}q^h_{k,j},
\tag{9}
\]

and define the prescribed Bellman defect, with one fixed sign convention, by

\[
p^h_k:=u^h_k-F_r(x^h_k;u^h_{k+1}).
\tag{10}
\]

Assume

\[
m_h:=\max_{k,j}q^h_{k,j}\longrightarrow0,
\tag{11}
\]

\[
\epsilon_h:=\max_{k}\|u^h_k-s\|_\infty\longrightarrow0,
\tag{12}
\]

and the signed period seam closes relative to total hazard:

\[
{\left\|\sum_{k<K_h}p^h_k\right\|_\infty\over A_h}
\longrightarrow0.
\tag{13}
\]

Then a subsequence of the normalized cumulative hazards

\[
\lambda_{h,j}:={Q_{h,j}\over A_h}
\tag{14}
\]

converges to some `lambda in Delta(I)` satisfying

\[
\boxed{M\lambda=0.}
\tag{15}
\]

In particular, `lambda` is a homogeneous simplex-LCP witness:

\[
M\lambda\ge0,
\qquad
\lambda_i(M\lambda)_i=0\quad(i\in I).
\tag{16}
\]

The theorem assumes no Nash condition, no terminal approximation, no debt
closure, no endpoint-regret estimate, and no survival contraction.

The uniform anchor hypothesis (12) may be weakened to the coordinatewise
hazard-weighted condition

\[
\sum_{k,j}q^h_{k,j}|u^h_{k+1,i}-s_i|=o(A_h)
\qquad(i\in I).
\tag{17}
\]

For the formalization, (12) is a simpler sufficient interface.

### Fin4 hard-residual corollary

For `FinFourQuantitativeFullSupportHardResidual`, the checked field
`normalCore_eq_univ` identifies the normal-player matrix in
`ResidualHardClass.no_homogeneous` with the full normalized singleton matrix
`M`.  Therefore no family satisfying (9)--(13) exists in that residual.

Equivalently, a vanishing-mesh periodic word cannot have both annotations
converging to the own-singleton vector and a signed prescribed Bellman seam
which is sublinear in its total hazard.

## Conjecture-facing change

The source-closed endpoint cycle in the maintained `COMP` route is horizontal:
its static debt increments can circulate exactly, but an executable chronology
must also close its prescribed Bellman payoff equation.  The natural proposal
was to regularize the cycle by small product roots near a common local anchor.

Theorems A and B decisively remove the two anchors supplied by the current
hard-residual geometry.

1. Near the positive minimum fiber, small positively absorbing roots create a
   fixed all-behavior Never gain.
2. Near the own-singleton vector, signed prescribed period closure forces the
   homogeneous LCP branch explicitly excluded by the hard residual.

Theorem B begins before approximate Nash and before debt closure.  It is
therefore not the earlier diagnostic statement that an already supplied
terminal-approximating family has an LCP limit.  It is an algebraic no-go for
the proposed prescribed-payoff producer itself.

The remaining chronological producer must use at least one feature absent
from this local scheme: a macroscopic payoff excursion, a different or
phase-dependent anchor, a period seam comparable to the clock charge, a
singular clock which fails the intended shadowing contraction, or an actual
minimum-fiber support exit.

## Definitions, probability, and agency

All root laws are independent products and are executed on the unique live
all-Continue history.  In Theorem A, `u_k` denotes the actual infinite-tail
payoff, not an annotation.  The cap `B_i` is the supremum over every unilateral
behavioral replacement.  The proof uses the single admissible complete
replacement `Never`, so (6) is a lower bound against the unrestricted class
without a best-response-attainment claim.

Theorem B is an identity about candidate Bellman annotations and product-root
laws.  It makes no behavioral optimality claim.  The root successor operator
`F_r(x;u)` includes terminal rewards on every nonempty quitting coalition and
the continuation `u` on all-Continue.

## Proof of Theorem A

Fix `i`.  Let `v_{k,i}` be the payoff when `i` replaces its complete strategy
by `Never`, starting from phase `k`, and put

\[
G_{k,i}:=v_{k,i}-u_{k,i}.
\]

For `T subseteq I\{i}`, let `P_{k,-i}(T)` be the probability that exactly the
opponents in `T` Quit at phase `k`.  Subtracting the prescribed and Never
Bellman equations gives

\[
\begin{aligned}
G_{k,i}={}&\beta_{k,-i}G_{k+1,i}
+q_{k,i}\beta_{k,-i}(u_{k+1,i}-s_i)\\
&+q_{k,i}\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
P_{k,-i}(T)\bigl(r_i(T)-r_i(T\cup\{i\})\bigr).
\end{aligned}
\tag{18}
\]

The last line is at least

\[
-2R q_{k,i}(1-\beta_{k,-i}).
\]

Moreover,

\[
1-\beta_{k,-i}
\le\sum_{j\ne i}q_{k,j}
\le(n-1)m.
\]

Using (3)--(4) in (18),

\[
G_{k,i}\ge
\beta_{k,-i}G_{k+1,i}+{\eta\over2}q_{k,i}.
\tag{19}
\]

Deleted-player contraction follows from the stated assumptions.  If

\[
\prod_{k<K}\beta_{k,-i}=1,
\]

then every opponent of `i` Continues surely in every phase.  Joint contraction
(5) makes `i` Quit alone eventually with probability one, so its actual payoff
at every phase is `s_i`, contradicting (3).  Thus every deleted turn contracts.

Iterating (19) removes the bounded terminal remainder.  If `W_t` and
`W_{t,-i}` denote joint and deleted survival before the infinite phase index
`t`, then

\[
G_{0,i}\ge{\eta\over2}\sum_{t\ge0}W_{t,-i}q_{t,i}.
\tag{20}
\]

Since `W_{t,-i}>=W_t` and eventual joint absorption is one,

\[
\begin{aligned}
\sum_i\sum_tW_{t,-i}q_{t,i}
&\ge\sum_tW_t\sum_iq_{t,i}\\
&\ge\sum_tW_t(1-\beta_t)=1.
\end{aligned}
\tag{21}
\]

Some player has the sum in (20) at least `1/n`, proving (6).

## Proof of Theorem B

Put

\[
a_{h,k}:=\sum_jq^h_{k,j}.
\]

For each coordinate `i`, the finite product expansion has the uniform form

\[
F_{r,i}(x^h_k;u^h_{k+1})-u^h_{k+1,i}
=\sum_jq^h_{k,j}M_{ij}+e_{h,k,i},
\tag{22}
\]

where, for some constant `C` depending only on the finite reward table and an
eventual bound on the annotations,

\[
|e_{h,k,i}|
\le a_{h,k}\epsilon_h+C a_{h,k}^2.
\tag{23}
\]

Indeed, the singleton terminal mass owned by `j` differs from the raw hazard
`q^h_{k,j}` by at most quadratic total hazard, every nonsingleton coalition
has total probability at most quadratic total hazard, and the all-Continue
coefficient contributes the displayed annotation error.

Although the periods may vary,

\[
\sum_k a_{h,k}^2
\le n m_h\sum_k a_{h,k}
=n m_hA_h=o(A_h).
\tag{24}
\]

Consequently

\[
\sum_k|e_{h,k,i}|=o(A_h).
\tag{25}
\]

Cyclicity gives

\[
\sum_k(u^h_k-u^h_{k+1})=0.
\]

Summing (10) and (22) therefore yields, up to the harmless sign fixed in
(10),

\[
MQ_h=-\sum_kp^h_k+o(A_h)=o(A_h).
\tag{26}
\]

The vectors `lambda_h=Q_h/A_h` belong to the finite simplex.  A convergent
subsequence has limit `lambda in Delta(I)`, and division of (26) by `A_h`
proves (15).

## Boundary tests

- The singleton floor in Theorem A is essential.  With one persistent active
  owner and all opponents playing Never, positive absorption makes that
  owner's payoff exactly its singleton reward, so (3) fails.
- The small-root bound in Theorem A is what prevents collision rewards from
  repaying the assigned Quit loss.  At macroscopic hazards no bound of the
  displayed form is claimed.
- The solo anchor in Theorem B is essential.  At a general common anchor `v`,
  first-order closure gives
  `v_i=sum_j lambda_j r_i({j})`, not `M lambda=0`.
- Relative signed seam closure is essential.  A seam of order `A_h` can
  cancel a nonzero `M Q_h`, even if its unnormalized value tends to zero.
- Vanishing mesh is essential.  At fixed hazards, nonsingleton rewards enter
  the prescribed payoff at leading order.
- The period lengths and total hazards need not converge or remain bounded.
  Only each `K_h` is finite, `A_h>0`, and the row mesh tends to zero.
- If `M=0`, compatible tables admit small cyclic closures and (15) holds
  trivially, showing that the theorem does not manufacture a false
  obstruction in the homogeneous chamber.

## Source correspondence and novelty

The Fin4 singleton separation and tube are checked in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`,
notably
`exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal`.

The exact successor expansion is supported by
`abs_quittingRootSuccessorPayoff_sub_tail_sub_singletonLinearization_le` in
`UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`.
That file's
`hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks` is related but
does not subsume Theorem B: it requires aggregate absolute Bellman error and
endpoint regret to be little-o of total hazard.  Theorem B uses only the
signed period sum of prescribed Bellman defects; convergence to the special
solo anchor supplies the stronger equality `M lambda=0`.

The hard-residual contradiction uses `normalCore_eq_univ` from
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
and `ResidualHardClass.no_homogeneous` from
`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`.  The Lean proof
explicitly reindexes the full-player direction onto the normal-core subtype;
this is not definitional equality.

No external paper theorem is used.  A narrow repository search found no
existing signed-period solo-anchor theorem or minimum-tube Never bound with
these hypotheses.

## Adapter and remaining consumer

Theorem A applies directly to any proposed actual periodic chronology whose
phase payoffs remain in the checked minimum tube.  Theorem B applies to any
proposed annotated periodic word collapsing to the solo vector with relative
prescribed closure.  Their conclusion is impossibility in the maintained
Fin4 hard residual, so no further semantic consumer is required.

These are no-go theorems, not producers.  They do not construct the periodic
words from an arbitrary hard residual or from one endpoint monodromy.  Their
strict contribution is to eliminate the two natural local-anchor producer
classes from the maintained `COMP` obligation.

The following remain open and are not asserted exhaustive:

1. a different or phase-dependent common anchor;
2. a signed period seam comparable to total hazard;
3. a singular clock whose loss is too small for two-clock shadowing;
4. candidate annotations which do not shadow actual periodic phase values;
5. a macroscopic excursion without a source-matched return; and
6. a minimum-fiber replacement satisfying the no-new-support and
   vanished-debtor rank passport.

## Checked Lean realization

Theorem A is checked in
`Research/Quitting/LocalPeriodicAnchorObstructions.lean`.  Its exact packet
structure is `LocalPeriodicAnchorPacket`; the collision estimate is
`quittingRootContinue_sub_quit_ge_singletonGap_mul_survival_sub_collision`,
the deleted-player contraction is
`quittingPeriodicDeletedProduct_lt_one_of_payoff_gap`, and the finite-cycle
aggregate is exposed by
`exists_quittingPeriodicBehavioralGap_of_payoff_gap`.  The reader-facing
conclusions are `localPeriodicAnchor_obstruction` and
`localPeriodicAnchor_theoremA`.  They use unrestricted behavioral caps through
`quittingPeriodicNeverPayoff_le_behavioralCap`.

The packet fields are exactly the supplied numerical data: reward bound,
phasewise singleton gap, hazard bound, positive full-cycle absorption, and
`R_nonneg`, `eta_pos`, and the cardinality bound.  The former supplied
`never_gap` field is no longer present: the checked proof derives the
playerwise contraction and applies
`Math.FiniteCycleAggregate.exists_player_base_ge_eta_div_two_card`.

Theorem B and its Fin4 hard-residual corollary are checked in
`Research/Quitting/FinFourPeriodicAnchorResidualAdapter.lean`.  The packet
structure is `FinFourPeriodicAnchorPacketFamily`, and the headline theorem is
`finFourPeriodicAnchor_false_of_packet_family`.  The preceding pointwise
version is `finFourPeriodicAnchor_false_of_returnedProductBlock_family`.
The fixed-matrix bridge is
`QuittingReturnedProductBlock.square_linearization_bound`; compactness and
subsequence production use
`MathUE.LocalPeriodicAnchor.exists_normalizedHazard_subsequence_kernel_of_eventually_additive_norm_seam`.
The final hard-residual contradiction is
`finFourNormalizedKernel_false_of_residualHardClass`.

These declarations establish `M` for the stated conditional results.  They do
not provide an arbitrary-game periodic chronology (`A`), and they have no
downstream conjecture consumer (`C`): periodic blocks, roots, and annotations
remain supplied by the caller.  The adapter also does not claim best-response
attainment or a uniform-equilibrium payoff.

## Scope and nonclaims

The results do not use the strict principal-face blocker and do not enlarge
the projective-Q-bar class.  They do not exclude all local anchors, all
varying-period constructions, or the one-active exceptional-owner mechanism.
They do not construct a macroscopic excursion, an admissible return, a lower
minimum-fiber point, or a terminal approximate equilibrium.
