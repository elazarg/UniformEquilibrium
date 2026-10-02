# Adversarial audit of the strict-ray orientation

## Verdict

Sections 2, 4, and 5 contain useful and mostly correct reductions, subject to
two scope qualifications below.  Section 3 has a decisive gap: the signed
block displacement in (9) does not imply the collision-work conclusion

\[
h_i<0,\qquad \lambda_i=0.
\]

Cap displacement and collision work are different first-order quantities.
The former is controlled by the solo matrix; the latter also contains the
collision matrix.  The equations displayed in the packet provide no bridge
between them.  Consequently the final proposition in Section 5 is not the
residual obtained from the preceding argument, and the packet is not ready
for export in its present form.

The periodic cap-near-return lemma itself appears sound and potentially worth
retaining as a separate theorem after its nondegeneracy hypotheses and word
orientation are made explicit.

## Claim audited

The packet proposes to consume a strict maximal-prefix ray when finite exact
cap blocks have cap displacement negligible relative to every deleted-player
absorption.  On failure, it claims to extract a fixed player and sign and then
identify that obstruction with a missing current-hazard coordinate carrying
strict negative normalized collision work.  It finally records several
quantities that cannot rank a coherent positive-root ray and asks for a
source transition consuming the alleged negative-work seam.

## Sources inspected

The audit used the following checked interfaces.

- `quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_eq` and
  `quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq` in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`.
- `QuittingMaximalCapSemanticPrefixRayStall.weightedAbsorption_hasSum`,
  `absorption_tsum_le_exact_debtDrop`, and the absorption-tail results in
  `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`.
- `FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayPaidGain_eq_survival_mul`
  in
  `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`.
- `QuittingForwardExactCapTail`, `tailAverage_renewal`, and
  `eventually_currentHazard_supported_binding` in
  `Research/Quitting/ForwardExactCapTailFlow.lean`.
- `cap_increment_eq_normalizedSolo_add_error`,
  `capGap_eq_soloTailFlow_add_errorTail`, and `tailNormalizedCapFlow` in
  `Research/Quitting/ForwardExactCapTailFirstOrder.lean`.
- `FinFourStrictRayForwardExactCapTail.analysis` in
  `Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean`.
- The current one-step regeneration interface in
  `Research/Quitting/PaidCapMaximalOneStepRegeneration.lean` and the
  independent audit of the supplied coherent-ray extension in
  `feedback/REST_REGEN_PR86__BY_GATE_FALSIFIER.md`.

## 1. Application of the periodic lemma

The canonical cap orbit has the required exact identities.  With the packet's
prefix convention, the block

\[
W_{K,N}=q_{N-1}*\cdots*q_K
\]

maps continuation cap `b_K` to `b_N`.  Backward induction through the exact
cap--Nash roots gives the finite-block optimal-response identity required by
Section 1.  The exact coordinate debt scaling also gives (7):

\[
U_i(N)-U_i(K)
=b_{N,i}-b_{K,i}+(1-c(W_{K,N}))d_i(K).
\]

There is, however, a missing hypothesis in (8).  Positive total absorption of
each selected root does not imply

\[
1-c_{-i}(W_{K,N})>0
\]

for every player.  A block whose Quit hazards are all carried by one player
has `c_{-i}=1` for that player.  The displayed ratios are then undefined, and
the contraction proof of the periodic behavioral cap does not apply to that
coordinate.  The theorem must either:

1. quantify only over blocks having positive opponent-generated absorption
   for every player; or
2. define an extended-real convention and dispatch zero denominators before
   invoking the periodic lemma.

Calling this a later ``deleted-clock subsidiary possibility'' does not repair
the statement of (8); it is a prerequisite for forming the ratios.

Subject to that repair, the near-return implication is sound.  It supplies
terminal approximate Nash profiles against unrestricted behavioral
deviations, not merely stationary ones.

## 2. Exact content of failure of near-return

Assume all denominators under consideration are positive and set

\[
\Phi(K,N)=
\max_i\frac{|b_{N,i}-b_{K,i}|}{1-c_{-i}(W_{K,N})}.
\]

If the nonnegative liminf in (8) is not zero, then some `kappa > 0` and all
sufficiently large `K` satisfy

\[
\Phi(K,N)\ge\kappa\qquad\text{for every }N>K.
\]

After choosing any cofinal sequence of such blocks, finite pigeonhole on the
four coordinates and two signs does yield a subsequence satisfying (9).
Thus the fixed-coordinate, fixed-sign **block cap seam** is valid after the
denominator repair.

What it does not give is a local normalized collision-work seam.  Even taking
`N` to infinity, the checked cap telescope identifies the leading object as

\[
(M\Lambda)_i,
\]

up to the normalized error tail.  For a one-step block the leading object is
instead `(M lambda)_i`.  The collision-work vector is

\[
h=M\Lambda+\rho J\lambda.
\]

The additional term `rho J lambda` is precisely the endpoint/collision term;
it is not controlled by signed cap displacement.

## 3. Falsification of the implication to (10)

There is already a checked canonical maximal-ray regression exhibiting the
same separation, albeit behind the project's explicit `D_* = 0` fence.  In
`Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean`, the rational
three-active completion has cap coordinates `(a_k,a_k,b_k,...)` and selected
maximal hazards `(t_k,t_k,z_k,0)`.  The checked invariant calculations give

\[
a_{k+1}<a_k/2,\qquad z_k<t_k,\qquad
t_k\le (5/4)b_k\le(5/4)a_k.
\]

For active player 0, the block of one row therefore has

\[
|a_{k+1}-a_k|>a_k/2,
\]

while its opponent-generated absorption is at most

\[
1-(1-t_k)(1-z_k)\le t_k+z_k<2t_k\le(5/2)a_k.
\]

Hence the signed block seam is bounded below by `1/5` at every date.  But
player 0's normalized current hazard is

\[
\frac{t_k}{2t_k+z_k}>1/3,
\]

so every normalized cluster has `lambda_0 > 0`, and limiting
complementarity forces `h_0=0`.  Thus maximal-root selection itself does not
turn this kind of cap seam into (10).  The regression is not a counterexample
to a theorem that genuinely uses positive global minimum debt: it has
`D_*=0`.  It does show that such a theorem would need a new, explicit use of
positive-minimum source provenance; neither the block seam nor maximality nor
the displayed normalized identities suffices.

Independently, the displayed normalized equations admit the following even
simpler algebraic configuration.

On two coordinates take

\[
\lambda=\Lambda=(1/2,1/2),\qquad \rho=1/2,
\]

\[
M=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
J=\begin{pmatrix}0&-2\\-2&0\end{pmatrix}.
\]

Then

\[
M\Lambda=(1/2,1/2),
\qquad
h=M\Lambda+\rho J\lambda=(0,0).
\]

Thus there is a strictly positive solo cap-flow seam in both coordinates,
while every coordinate is present in `lambda` and every collision-work
coordinate is zero.  The relevant row data are compatible with ordinary
quitting rewards: for player 1, for example, take

\[
r_1(\{1\})=0,\quad r_1(\{2\})=1,\quad
r_1(\{1,2\})=-1,
\]

and use the symmetric data for player 2.  This gives `M_12 = 1` and
`J_12 = -2`.  The example is not asserted to be a positive-minimum Fin4
canonical ray; it is enough to show that the algebra cited between (9) and
(10) cannot prove the implication.  Padding it by inactive coordinates does
not create the missing identity.

The valid conclusion from (9) is therefore a signed cap-flow condition,
schematically

\[
|(M\Lambda)_i|\gtrsim \kappa(1-\Lambda_i),
\]

for suitably chosen tail blocks, or the corresponding current-flow statement
for one-step blocks.  Turning this into `h_i < 0` requires a new estimate on
the collision term or on endpoint slack.  Complementarity alone gives only

\[
h\le0,\qquad \lambda_i h_i=0;
\]

it cannot convert a cap-flow seam into strict work or force `lambda_i=0`.

## 4. Exact-scaling and rank claims

For one fixed coherent positive-root regeneration ray, the formulas

\[
d_i(n)=s_nd_i(0),\qquad D_n=s_nD_0
\]

are correct, and the coherent paid-row transport gives `G_n=s_n G_0`.
Positive global minimum debt forces a positive lower bound on `s_n`; hence
positive-debt support, normalized debt, and gain/debt density are constant,
and positive total absorption is summable.  These facts genuinely rule out
the particular rank proposals listed in Section 4.

Two qualifications should be recorded.

- On current main, the generic canonical forced-pair theorem states
  `rayPaidGain(index) = survival(index) * rayPaidBaseGain(index)`, and the base
  gain may depend on `index`.  The stronger formula `G_n=s_nG_0` belongs to the
  separately supplied recursively coherent paid/reset ray.  The packet must
  name that hypothesis rather than silently identify the two ray objects.
- The calculations do not prove that **no** well-founded rank exists.  They
  exclude support, normalized-debt, fixed-label, gain-density, and raw
  absorption-budget ranks.  A rank using root faces, binding strata, or an
  external connector is untouched.

## 5. Section 5 and the corrected residual

The pure-pair screening statement is sound: behind a pure nonsingleton root,
changing the tail cannot alter prescribed payoffs, unrestricted unilateral
caps, debt, or terminal law.  The warning that a horizontal sure-absorption
cycle is not a chronological block is also correct.  Same-law regeneration
does not by itself create a pre-pair cap-reset seam.

But the proposed final residual starts from (9)--(10), and (10) has not been
derived.  The honest remaining question is instead:

> Starting from a fixed-coordinate signed **block cap-flow seam**, together
> with the retained forced-pair atom and paid row, either relate the seam to
> strict endpoint work by a new quantitative theorem, consume it directly by
> a positive-reach cap reset, or produce a renewable binding/source descent.

The three alternatives printed at the end of Section 5 may be useful targets,
but they are not presently proved exhaustive.

## Disposition

Retain the periodic cap-near-return lemma and the exact-scaling rank no-gos as
internal mathematics after the qualifications above.  Remove or replace the
claim that failure gives `h_i < 0` and `lambda_i = 0`.  A revised packet could
be reviewed again, but `ORIENT_FIN4.md` should not enter `exports/` as written.
