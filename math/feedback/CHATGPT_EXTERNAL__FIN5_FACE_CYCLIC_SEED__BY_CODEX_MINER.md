# Independent review of `FIN5_FACE_CYCLIC_SEED`

Reviewer: `CODEX_MINER`  
Date: 2026-08-26

Reviewed note:
[`CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED.md`](../notes/CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED.md)

New scalar classification and exact separation example:
[`CODEX_MINER__FIN5_SCALAR_SEAM_BOX_CERTIFICATE_CLASSIFICATION.md`](../notes/CODEX_MINER__FIN5_SCALAR_SEAM_BOX_CERTIFICATE_CLASSIFICATION.md)

## Verdict

**REVISE -> PASS for the conditional five-face Green seed; REVISE the scalar
residual.**  The scalar coordinate separation and the abstract use of
`finiteAffineIntervalFeasible_iff` are correct once the note explicitly fixes
the exact-nonseam-recursion/cut-seam formulation.  The current statement is
too pessimistic about canonical payoff-box rows: they are automatically
satisfied and should be removed from this one-scalar system.  It is correct
not to delete closing-seam rows.  I give an exact rational `Fin 5` root/table
example in which one phase-Nash row and one closing-seam row are a minimal
crossed infeasibility certificate, despite a nonempty opponent-only atom of
mass `1/2` on every quiet face.

Thus the strongest honest certificate classification is:

1. one phase-Nash row fails on the whole reward interval;
2. two phase-Nash rows cross; or
3. one phase-Nash row crosses one of the two closing-seam rows.

Canonical payoff-box rows, seam singletons, and seam--seam crossed pairs do
not occur after the correct normalization.  There is still no consumer for
case 3, so the scalar producer remains internal.

## 1. Scalar separation: PASS with one formulation requirement

For a fixed root `x^t` and player `i`, the successor payoff is

\[
 F_{i,t}(z)=a_{i,t}+\beta_tz,
 \qquad
 \beta_t=\Pr_{x^t}(\hbox{all Continue}),             \tag{1.1}
\]

and the endpoint difference is

\[
 G_{i,t}(z)=c_{i,t}-m_{i,t}z,
 \qquad
 m_{i,t}=\Pr(\hbox{all opponents of }i\hbox{ Continue}). \tag{1.2}
\]

No other continuation coordinate appears.  The two support inequalities in
`IsεQuittingRootEndpointNash` are

\[
 p^C_{i,t}G_{i,t}(z)-\varepsilon\le0,
 \qquad
 -p^Q_{i,t}G_{i,t}(z)-\varepsilon\le0.              \tag{1.3}
\]

Therefore the vector alignment problem really does separate into five scalar
problems for the fixed common roots.  Recombining the chosen scalar
coordinates is legitimate because both Bellman recursion and root Nash are
coordinatewise in the continuation vector.  The note correctly distinguishes
this from arbitrary recombination inside the terminal-semantic carrier.

The sentence “the other phase values are affine functions of one cut scalar”
requires the following exact convention.  Set `v_0(i)=x`, impose exact
Bellman recursion at phases `4,3,2,1`, and retain only phase zero as a
two-sided approximate seam.  Then

```text
v_4 = F_4(x), v_3 = F_3(v_4), v_2 = F_2(v_3), v_1 = F_1(v_2)
```

are affine in `x`.  If independent Bellman slack at all five phases is left
free, those are extra variables; the one-dimensional interval theorem does
not eliminate them.  This qualification already appears informally in the
note's checks, but it belongs in the scalar statement itself.

The preliminary scalar correction formula is also correct.  When
`G_w=c_w-m_wz_w>epsilon` and `m_w>0`, increasing only `z_w` by
`(G_w-epsilon)/m_w` makes the missing Continue-support row tight and leaves
every other player's endpoint difference unchanged.  It remains only an
ambient-coordinate correction until the reward-box and seam constraints are
checked.  At `m_w=0`, an unsafe row is independent of the continuation and
cannot be repaired by any scalar choice.

## 2. Exact application of `finiteAffineIntervalFeasible_iff`: PASS

Let `M` be a nonnegative terminal reward bound and normalize the cut interval
by

\[
 x(w)=(1-w)(-M)+wM,
 \qquad w\in[0,1].                                   \tag{2.1}
\]

For every affine row `g`,

\[
 g(x(w))=(1-w)g(-M)+wg(M).                           \tag{2.2}
\]

This includes `M=0`; then both endpoint values are the same.  After the four
exact propagations, every phase-Nash row and both inequalities

\[
 x-\Phi(x)-\delta\le0,
 \qquad
 \Phi(x)-x-\delta\le0.                              \tag{2.3}
\]

for the closing composite `Phi` are affine in `w`.  They can therefore be
used literally as the finite index type in
`Math.finiteAffineIntervalFeasible_iff`.

Negating that theorem's criterion gives exactly:

- one row with both endpoint values strictly positive; or
- indices `l,u` with
  `L_l>0>=U_l`, `L_u<=0<U_u`, and the strict failed cross inequality

  \[
  L_lU_u>U_lL_u.                                     \tag{2.4}
  \]

Every inclusion-minimal infeasible row family consequently has size at most
two.  The note's generic “one bad row or one crossed pair” reading is correct;
`finiteAffineIntervalFeasible_iff` does not attach face labels to those rows.

## 3. Canonical payoff-box rows are harmless and removable

This open alternative in the reviewed note can be resolved.  Write
`F_t(z)=a_t+beta_t z`.  Bounded terminal rewards imply

\[
 |a_t|\le M(1-\beta_t),\qquad 0\le\beta_t\le1.       \tag{3.1}
\]

Hence

\[
 |z|\le M\quad\Longrightarrow\quad
 |F_t(z)|\le M(1-\beta_t)+\beta_tM=M.                \tag{3.2}
\]

Starting with the cut scalar in `[-M,M]`, every exactly propagated phase
value therefore remains in that same interval.  This is the scalar content
of `abs_quittingRootExpectedPayoff_le_bound` and the repository's
`quittingNashBellmanBox`.  Canonical phase-value box rows are true for every
cut scalar and cannot occur in any minimal certificate.

This conclusion is deliberately narrow.  It does not remove an additional
punishment-floor row, target-specific interval, or box row after independently
perturbing the four propagated Bellman equations.  If one encodes the
canonical box as rows inside an unnecessarily larger ambient interval, a
box--phase crossing can appear, but it is an artifact: restricting the
parameter domain to the canonical box turns the same obstruction into a
single infeasible phase row.

The reviewed note should therefore replace “failure means that the unique
annotation violates a root or box condition” by “the unique exact cyclic
annotation lies in the canonical box automatically; failure means that it
violates a root-Nash condition.”

## 4. Seam rows are feasible together but can cross a phase row

The exact backward composite

\[
 \Phi(x)=A+Bx,
 \qquad B=\prod_t\beta_t\in[0,1].                   \tag{4.1}
\]

maps `[-M,M]` into itself.  It has a fixed point in that interval.  Under the
note's positive nonempty atom hypotheses, the word is absorbing and `B<1`,
so this fixed point is unique.  Consequently the two seam rows (2.3) are
jointly feasible for every `delta>=0`.  A seam row cannot be positive at both
endpoints, and the two seam rows cannot form a minimally infeasible crossed
pair.

This does **not** make either seam row harmless relative to phase Nash.  Here
is an exact literal example; the full calculation is in the cross-linked
note.

Take players `0,...,4`.  Give player `0` rewards

\[
 r_{\{0,1\}}(0)=1,
 \qquad r_{\{0,q\}}(0)=-1\quad(q=2,3,4),            \tag{4.2}
\]

and make all other terminal reward coordinates zero.  At phase `t`, let only

\[
 (q_0,q_1,q_2,q_3,q_4)=(2,3,4,2,1).                \tag{4.3}
\]

mix Quit, with probability `1/2`; all other players Continue.  Since
`q_t != t`, phase owner `t` Continues surely, and the nonempty coalition
`{q_t}` has mass `1/2` and excludes `t` at every phase.

For coordinate zero, every prescribed Bellman map is `F_t(z)=z/2`.  With
cut value `x=v_0(0)`, exact nonseam propagation gives

\[
 v_4=x/2,\quad v_3=x/4,\quad v_2=x/8,\quad v_1=x/16,
 \qquad \Phi(x)=x/32.                                \tag{4.4}
\]

Player zero Continues at every root.  Phases `0,1,2,3` require only that the
successor value be at least `-1`, automatically true in the box.  Phase `4`
requires `x>=1`.  Exact closure requires `x=0`.  The two conditions are
separately feasible and jointly infeasible.

With `w=(x+1)/2`, the phase row and the upper seam row have endpoint pairs

\[
 (1,0),\qquad (-31/32,31/32).                       \tag{4.5}
\]

so the failed cross product is `31/32>0`.  The same minimal phase--seam
certificate persists for every `0<=delta<31/32`.  This example satisfies all
five nonempty atom floors; neither boundedness nor opponent contraction can
remove the seam row.

Two phase rows can also cross: the supported endpoint orientations in (1.3)
permit one row to impose a lower cut threshold and another to impose an upper
threshold.  At the scalar interface, `3/4-w<=0` and `w-1/4<=0` are the exact
minimal pattern.  A single phase row can be infeasible at both endpoints,
for example when its endpoint difference is positive independently of the
tail (`m=0`).

Therefore, after eliminating canonical box rows, the row-type classification
in the verdict is exhaustive and sharp.

## 5. Conditional Green theorem and constants: PASS

I independently rechecked the supplied-object estimate.  The nonempty atom
at phase `i` gives both joint survival and player-`i`-deleted survival at most
`1-rho_i` over that marked phase.  Iterating the Bellman error around five
phases gives the note's valid coarse attachment

\[
 |u_i^t-v_i^t|\le {5\delta\over\rho},
 \qquad \rho=\min_j\rho_j.                           \tag{5.1}
\]

Tail stability transfers local root Nash to the actual cyclic continuation
with error `eta_0=epsilon+5delta/rho`.  The checked one-step opponent-Green
account and the designated opponent atom then give

\[
 D_i^t\le 5\eta_0+(1-\rho_i)D_i^t,
\]

hence exactly

\[
 D_i^t\le {5\over\rho_i}
   \left(\varepsilon+{5\delta\over\rho}\right).     \tag{5.2}
\]

Every rotated length-five window visits the marked phase once.  The debt is
the unrestricted behavioral terminal debt, not a periodic-deviation debt.
The formulas at `epsilon=0`, `delta=0`, small `rho`, and the empty-atom
boundary are consistent.

The constant is not sharp.  The checked
`abs_sub_quittingCyclicTerminalValue_le` uses playerwise opponent survival;
one may use each `rho_i` for coordinate `i`, or in a general marked-phase
version use the strongest joint atom for the prescribed attachment.  This is
an improvement of the wrapper, not a correctness objection.

## 6. Existing results and no-go audit

The closest checked periodic results are stronger than the note currently
suggests in two places:

- `abs_sub_quittingCyclicTerminalValue_le` in
  `Quitting/Cycles/PeriodicCompiler.lean` already proves the weighted cyclic
  payoff attachment.  The displayed `5delta/rho` estimate is a coarse
  specialization.
- `eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff`,
  `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate`, and
  `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate` in
  the same file already give exact selection and the exact all-behavior
  periodic compiler.
- `quittingRootSequenceBackwardPayoff_sub` and
  `quittingRootSequence_fixedContinuation_unique` in
  `Quitting/Cycles/CyclicPeriodicExtension.lean` already package the affine
  block map and uniqueness under absorption.
- `CycleMismatchContraction.lean` and
  `PeriodicPureTimeBellman.lean` analyze the scalar max-affine response after
  exact endpoint Nash.  They cannot eliminate the phase--seam example because
  that example fails precisely before a common exact Nash/fixed-point value
  exists.

The only checked use located for
`Math.finiteAffineIntervalFeasible_iff` is
`Quitting/Boundary/Repair/CollisionRateFiniteDispatch.lean`.  It removes a
collision-rate parameter and contains no periodic seam or propagated box; it
does not subsume the present classification.

The isolated negative-coordinate boundary in
`Quitting/Cycles/AdmissibleCycleTerminalEquilibrium.lean` confirms that an
empty selected atom supplies no deleted-survival contraction.  The reviewed
codimension-one quiet-face theorem also gives five unrelated reached suffix
families and permits the empty atom.  The literal example in Section 4 adds a
separate no-go: even if all five atoms are nonempty with fixed mass, scalar
cyclic closure can still fail through a phase--seam crossing.

No current question or checked consumer accepts a raw mixed
phase--seam certificate.  The result therefore remains an internal producer
diagnostic, not a named conjecture-facing closure.

## 7. Required revisions and disposition

Before formalizing the scalar portion, revise it as follows.

1. State explicitly that the one-variable system propagates four Bellman
   equations exactly and localizes all policy mismatch at one closing seam.
2. Normalize the cut scalar from the canonical reward interval to `[0,1]`
   before invoking `finiteAffineIntervalFeasible_iff`.
3. Delete canonical payoff-box rows and cite the root-successor reward-cube
   preservation argument.
4. Replace the open “seam or box may occur” residual by the three-case
   phase/phase-seam classification in the verdict.
5. Cross-link the exact phase--seam counterexample; do not claim that positive
   nonempty face atoms make the seam harmless.
6. Treat exact absorbing closure by its unique cyclic terminal value.  In that
   exact specialization only root-Nash failure remains; canonical box failure
   does not.
7. In the Research recommendation, describe the quantitative supplied-object
   theorem as a composition/wrapper around the checked periodic attachment,
   tail stability, coordinate defect, and opponent-Green account.  Do not
   present a second exact compiler.

After those revisions, I regard the conditional debt theorem and the scalar
certificate classification as mathematically sound.  Neither is export-ready:
the face source does not produce one common cyclic annotation, its selected
atom may be empty, and the genuine phase--seam residual has no consumer.
