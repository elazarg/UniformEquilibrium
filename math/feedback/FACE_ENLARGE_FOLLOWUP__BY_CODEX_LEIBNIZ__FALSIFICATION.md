# Falsification review of the two local periodic obstructions

Reviewed source: [`../FACE_ENLARGE_FOLLOWUP.md`](../FACE_ENLARGE_FOLLOWUP.md)

Reviewer identity: Codex Leibniz

## Claim restatement

I checked two claims independently.

1. A periodic product profile whose actual phase payoffs stay uniformly above
   every player's own singleton reward, whose roots are uniformly small, and
   whose joint and player-deleted survival clocks contract has a fixed
   profitable `Never` deviation.  The proposed bound is

   \[
   \operatorname{Expl}\ge \frac{\eta}{2|I|}.
   \]

2. A family of finite returned product words whose root mesh tends to zero,
   whose phase annotations approach the own-singleton vector, and whose
   aggregate prescribed Bellman seam is little-o of total hazard forces a
   normalized cumulative hazard direction \(\lambda\) satisfying

   \[
   M\lambda=0,
   \qquad
   M_{ij}=r_i(\{j\})-r_i(\{i\}).
   \]

   This is a homogeneous simplex-LCP solution and is therefore impossible on
   the full-normal-core Fin4 hard residual.

Both claims begin before a terminal-approximation hypothesis.  The first
exhibits an actual unrestricted behavioral deviation.  The second uses only
prescribed Bellman closure and contains no Nash or endpoint-regret premise.

## Sources inspected

I inspected the following narrow dependency set.

- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` and
  `exists_open_exactAllContinueTube_and_debtMoat_minimumFiber` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`.
- `FinFourQuantitativeFullSupportHardResidual`, including
  `normalCore_eq_univ` and `residualHardClass.no_homogeneous`, in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
- `HasHomogeneousSimplexSolution` in
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean` and its
  underlying definition `SingletonLCPFeasible` in
  `MathUE/LinearProgramming/SingletonLCP.lean`.
- `QuittingReturnedProductBlock`,
  `hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks`, and
  `relativeError_gap_of_noHomogeneous` in
  `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`.
- The principal restriction adapters and hard-class specialization in
  `UniformEquilibrium/Quitting/Stationary/ReturnedBlockPrincipalRestriction.lean`
  and
  `UniformEquilibrium/Quitting/Classification/LCP/ReturnedBlockTangentGap.lean`.
- The export criteria in [`../exports/README.md`](../exports/README.md) and the
  live question
  [`../questions/POSITIVE_MINIMUM_FACE_CYCLE_ALIGNMENT.md`](../questions/POSITIVE_MINIMUM_FACE_CYCLE_ALIGNMENT.md).

No paper theorem is invoked by either proof.

## Verdict on the minimum-tube `Never` bound

The proof is correct, including its coverage of unrestricted behavioral
deviations: `Never` is one admissible complete behavioral replacement, so its
gain is a lower bound on the behavioral cap.  I found no counterexample.

For fixed player \(i\), subtracting the prescribed and `Never` Bellman
equations gives exactly

\[
\begin{aligned}
G_{k,i}={}&\beta_{k,-i}G_{k+1,i}
+q_{k,i}\beta_{k,-i}(u_{k+1,i}-s_i)\\
&+q_{k,i}\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
 P_{k,-i}(T)\bigl(r_i(T)-r_i(T\cup\{i\})\bigr).
\end{aligned}
\]

If \(|r_i(S)|\le R\), the last line is at least
\(-2Rq_{k,i}(1-\beta_{k,-i})\).  Hence the phasewise sufficient condition is

\[
(\eta+2R)(1-\beta_{k,-i})\le \eta/2.
\tag{A}
\]

The displayed mesh bound in the source implies (A), because

\[
1-\beta_{k,-i}\le (|I|-1)\max_{\ell,j}q_{\ell,j}.
\]

Iteration through the deleted-opponent clock is legitimate: all payoffs and
therefore \(G\) are bounded, so strict one-period deleted contraction removes
the terminal remainder.  Finally,

\[
\sum_i\sum_t W_{t,-i}q_{t,i}
\ge \sum_tW_t\sum_iq_{t,i}
\ge \sum_tW_t(1-\beta_t)=1,
\]

where the last equality uses joint contraction.  Pigeonhole gives the claimed
\(\eta/(2|I|)\) gain.

### Strengthening: deleted contraction is redundant

The separate player-deleted contraction hypotheses follow from the uniform
singleton floor and joint contraction.  If

\[
\prod_{k<K}\beta_{k,-i}=1,
\]

then every opponent of \(i\) Continues surely at every phase.  Joint
contraction then says that \(i\) has positive Quit probability somewhere in
the repeated turn.  Absorption consequently occurs almost surely at the
singleton \(\{i\}\), so the actual payoff of \(i\) at every phase is exactly
\(s_i\), contradicting \(u_{k,i}\ge s_i+\eta\).  Thus the theorem needs only
joint contraction, the floor, and the small-root condition.

The theorem should either assume \(|I|\ge2\) when using the displayed
denominator \(|I|-1\), or state the sharper phasewise condition (A).  For one
player, the floor and joint contraction are already incompatible, so the
intended conclusion is vacuous; the written division by \(|I|-1\) is still a
statement defect in ordinary mathematics.

### Boundary tests

- **One active clock.**  This is not a counterexample.  With only player \(i\)
  active, the repeated terminal coalition is \(\{i\}\) almost surely, so the
  assumed strict floor fails for \(i\).  This also explains the automatic
  deleted-contraction argument above.
- **Two players.**  The proof works unchanged.  Both clocks must occur in one
  turn under the floor and joint-contraction premises.
- **Variable period.**  No step uses a common bound on \(K\).  The result is
  stronger than the fixed-period formulation.
- **Collision accumulation.**  It is charged phase by phase through
  \(1-\beta_{k,-i}\); no interchange of expectation, stopping, or supremum is
  used.
- **Never mass.**  The prescribed periodic profile has no surviving Never
  event under joint contraction.  The unilateral `Never` strategy is handled
  directly through its deleted-opponent recursion.

The Fin4 adapter is honest: the checked minimum-fiber theorem supplies one
uniform positive singleton gap on the whole compact minimum fiber.  A smaller
neighborhood preserves half that gap.  Thus any periodic profile with actual
phase payoffs in that neighborhood and sufficiently small mesh has an actual
`Never` gain at least \(\delta/16\).

## Verdict on the solo-anchor closure theorem

The theorem is correct after making the prescribed residual explicit.  It is
stronger than the generic checked returned-block tangent theorem in one narrow
direction: it assumes only cancellation of the **sum** of prescribed Bellman
residuals, rather than little-o aggregate absolute Bellman error plus endpoint
regret.  The stronger conclusion is available because all annotations are
anchored at the singleton vector and the conclusion is the equality
\(M\lambda=0\), not merely LCP inequalities.

For a finite word indexed by \(k\), define

\[
p_k^h:=F(x_k^h,u_{k+1}^h)-u_k^h
\]

(the opposite sign gives the same norm hypothesis).  Cyclicity gives

\[
\sum_kp_k^h
=\sum_k\bigl(F(x_k^h,u_{k+1}^h)-u_{k+1}^h\bigr).
\tag{B}
\]

Write \(a_{h,k}=\sum_jq_{k,j}^h\),
\(A_h=\sum_ka_{h,k}\), and
\(m_h=\max_{k,j}q_{k,j}^h\).  Product expansion, uniformly in a possibly
varying number of phases, gives for every coordinate \(i\)

\[
F_i(x_k^h,u_{k+1}^h)-u_{k+1,i}^h
=\sum_jq_{k,j}^hM_{ij}+e_{h,k,i},
\]

with

\[
\sum_k|e_{h,k,i}|
\le C_R\sum_ka_{h,k}^2
+A_h\max_k|u_{k,i}^h-s_i|.
\tag{C}
\]

Here \(C_R\) may be any fixed constant large enough for the finite reward
bound and an eventual bound on the annotations.  Since

\[
\sum_ka_{h,k}^2
\le |I|m_hA_h,
\]

(C) is \(o(A_h)\).  Combining this with (B) and
\(\|\sum_kp_k^h\|=o(A_h)\) proves

\[
MQ_h=o(A_h),
\qquad Q_{h,j}=\sum_kq_{k,j}^h.
\]

The normalized vectors \(\lambda_h=Q_h/A_h\) lie in the simplex.  Compactness
and continuity give a subsequential limit \(\lambda\) with
\(M\lambda=0\).  This exactly supplies the nonnegative residual and
complementarity clauses of `SingletonLCPFeasible`.

### Strengthening: uniform annotation convergence is more than needed

It is sufficient to assume, for every payoff coordinate \(i\),

\[
\sum_{k,j}q_{k,j}^h|u_{k+1,i}^h-s_i|=o(A_h).
\]

Uniform convergence to \(s\) is one convenient sufficient condition.  The
hazard-weighted formulation admits a small collection of exceptional phases
provided they carry negligible first-order charge.

### Boundary tests

- **One player.**  The normalized matrix is zero, so the conclusion is true
  and supplies no obstruction, as expected.
- **One active owner.**  Then the limit is a simplex vertex and the theorem
  forces the entire corresponding column of \(M\) to vanish, not just its
  diagonal entry.  This is exactly why the one-owner case cannot evade the
  conclusion.
- **Phase bias.**  The limiting direction is the unweighted cumulative hazard
  across phases.  This is forced by the unweighted cyclic Bellman telescope;
  no stationarity or equal phase weighting is assumed.
- **Variable period and nonvanishing total charge.**  The proof uses only
  \(\sum_ka_{h,k}^2\le |I|m_hA_h\).  Thus \(K_h\) may diverge and \(A_h\)
  need not tend to zero.  Only positivity of \(A_h\), mesh convergence, and
  relative closure are required.
- **All-Continue limit.**  Every marginal may converge to Continue while the
  normalized cumulative hazard remains a nontrivial simplex point.  The
  normalization retains precisely that first-order direction.
- **Nonsingleton rewards.**  All collision contributions are absorbed in the
  \(o(A_h)\) term.  They may be arbitrary bounded numbers.
- **Unrestricted deviations.**  No deviation statement is made or needed.
  This theorem is genuinely pre-equilibrium: it concerns prescribed Bellman
  closure alone.

For the Fin4 hard residual, the formal adapter must explicitly transport the
full-player simplex witness through `normalCore_eq_univ` to the subtype matrix
`normalizedNormalPlayerMatrix`.  This is elementary reindexing, but it is not
definitionally the same object and should not be omitted from the Lean
handoff.

## Falsification summary

I tried the requested failure modes: one- and two-player boundaries, a single
active clock, varying periods, phase-concentrated hazards, positive or
vanishing total charge, accumulated collisions, nonuniform annotations, and
both Bellman-residual sign conventions.  None refutes either corrected claim.

The repairs are:

1. restrict the displayed mesh formula to \(|I|\ge2\), or use (A);
2. define the Bellman residual and its norm in the solo-anchor theorem;
3. state explicitly whether periods vary (the proof allows them to vary);
4. include the `normalCore_eq_univ` reindexing adapter; and
5. avoid saying that the strict face blocker produces either family.  It does
   not enter either proof.

## Export-gate verdict

The mathematics survives falsification, but neither claim currently passes
the export gate as a standalone packet.

- The minimum-tube theorem has a checked arbitrary-game adapter from a Fin4
  counterexample to a singleton-separated minimum tube, and it gives an
  actual all-behavior `Never` witness against every supplied local periodic
  profile.  What remains unproduced is such a periodic realization from the
  `COMP`/face-cycle data.
- The solo-anchor theorem removes a broader pre-equilibrium local ansatz, but
  likewise has no actual-data adapter from the face blocker or endpoint
  cycle.  It is a supplied-word obstruction.
- The live face-cycle question requires positive global minimality to
  eliminate a common-participant or scalar seam obstruction, or to reach an
  existing uniform-payoff consumer.  These theorems do neither.  They prove
  that two natural local regularizations cannot be the missing construction.

Accordingly, they are valuable Research results and should be formalized
there if desired, but they do not yet justify a new file in `exports/`.  An
exportable strengthening would derive from actual face-cycle or blocker data
an exhaustive alternative of the form: macroscopic source-matched excursion,
minimum-fiber rank exit, or one of the checked uniform-payoff consumers.

The scale-free Abel estimate and proposed full two-clock debt composition in
Sections 4--5 were not part of this assigned falsification.  Nothing in this
review certifies equation (27).
