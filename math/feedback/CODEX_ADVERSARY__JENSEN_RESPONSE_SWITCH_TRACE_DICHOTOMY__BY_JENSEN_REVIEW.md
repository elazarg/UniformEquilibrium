# Review of the Jensen response-switch trace dichotomy

**Reviewer:** `JENSEN_REVIEW`  
**Date:** 2026-08-31  
**Verdict:** **REVISE**

## 1. Claim reviewed

The note claims that one positive outsider cap-Jensen gap for an actual
quitting profile selects two supported deterministic clocks of the owner and
two approximately cap-optimal pure responses of the outsider such that:

- their symmetric response rectangle is positive by a fixed amount;
- the first response-disagreement date retains a fixed tail of the original
  owner law;
- the source retains fixed pair-deleted and full observer-opponent survival;
- one oriented edge is a literal paid first-disagreement row; and
- after cap lifting, an exactly zero debt of the reset owner remains zero at
  all finite prefixes and at the semantic-port limit.

For a sequence, the note then divides the disagreement dates into a fixed-date
arm and an escaping-date arm, the latter producing an all-`Never` opponent atom
only in a compact stopping-law limit. Section 6 claims an exact Fin4
regression showing that this compact obstruction need not be positive in the
finite-splice boundary product at any finite rank.

The source-visible switch theorem is mathematically correct after one missing
positivity hypothesis on the approximation error. The exact-zero corollary is
also correct for an **attained actual profile with exact owner debt zero**.
The blocking objection is its advertised reset-rigid use: the reset-rigid
question supplies a zero-debt **semantic carrier point**, generally represented
by actual profiles whose owner debts merely tend to zero. It does not supply
rankwise actual profiles of exactly zero owner debt. Thus the claim that the
reset owner remains identically zero through every rankwise paid-cap port is
not established from (R1)--(R6). A quantitative vanishing-debt repair is
available and is recorded in Section 6 below.

## 2. The response rectangle and unrestricted deviations

The deterministic-clock disintegration is sound for unrestricted behavioral
caps. For a fixed outsider response `q`, payoff is affine in the complete
stopping law of the distinct owner. Taking the supremum over all outsider
behavioral deviations only after this affine identity gives

\[
 B_i(\sigma)\le \mathbb E_T B_i(\sigma[T]),
\]

while pure-time extremality permits, for every supported `t`, a pure time
`q_t` satisfying

\[
 V_t(q_t)\ge B_i(\sigma[t])-\varepsilon.
\]

The expectation expansion is therefore correct:

\[
\begin{aligned}
\mathbb E_{T,S} A(T,S)
&=\mathbb E_TV_T(q_T)-
  \mathbb E_S\mathbb E_TV_T(q_S)\\
&\ge \mathbb E_TB_i(\sigma[T])-\varepsilon-B_i(\sigma)
 =J_i-\varepsilon,
\end{aligned}
\]

and symmetry gives `E R >= 2(J_i-epsilon)`. This argument really uses the
unrestricted behavioral cap; no bounded-controller or stationary-response
substitution occurs.

Two accompanying bounds are also correct:

- `A(t,s) >= -epsilon`, because `q_t` is approximately optimal at its own
  component and `q_s` is an admissible pure response there;
- `|R(t,s)| <= 4M`, because each of its four payoff terms lies in `[-M,M]`.

There is, however, a literal quantifier error in Theorem 3.1. The hypothesis
must be

\[
 0<\varepsilon\le\eta/4,
\]

not merely `epsilon <= eta/4`. A nonattained pure-time supremum need not admit
an exact `epsilon = 0` maximizer, and a negative approximation error is
impossible. Nothing later requires a stronger restriction.

## 3. Tail selection and all constants

The tail-quantile lemma is correct. With

\[
 p(t)=\pi\{u:u\ge t\},
\]

the set `{t : p(t) < c}` is an upper tail of
`Nat union {Never}` and has probability at most `c`.

If two response times first disagree at `r` and both sampled owner clocks are
strictly before `r`, owner absorption screens the response difference at both
components, hence `R=0`. Therefore

\[
 \Pr(p(r)<c,\ R\ne0)\le
 \Pr(p(T)<c)+\Pr(p(S)<c)\le2c.
\]

Set `c=eta/(16M)`. Since every cap and prescribed payoff lies in `[-M,M]`,
`J_i <= 2M`, so `eta <= 2M` and the quantile lemma applies. If no supported
pair satisfied both `R >= eta/2` and `p(r) >= c`, then

\[
 \mathbb E R
 \le \eta/2+4M(2c)=\eta,
\]

whereas `J_i >= eta` and `epsilon <= eta/4` give

\[
 \mathbb E R\ge2(\eta-\varepsilon)\ge3\eta/2.
\]

Thus (3.3)--(3.4) and their constants are correct. Orienting the pair loses a
factor two, so the receiving gain `eta/4` in (3.5) is also correct. The
receiving owner clock must satisfy `a >= r`, since otherwise both outsider
responses agree until the sure owner absorption and their receiving payoff
difference is zero.

The trace step is correct as ordinary mathematics. For

\[
 G(P)=V_P(q_a)-V_P(q_b),
\]

replacing the owner's complete law from the deterministic clock `b` to `a`
is the amplitude-one case of the one-edge trace estimate. The deleted event
omits both the owner and observer and hence has exactly the same probability
at `sigma`, `sigma[a]`, and `sigma[b]`. Moreover

\[
 G(\sigma[a])-G(\sigma[b])
 =A(a,b)+A(b,a)=R(a,b).
\]

Consequently

\[
 H_{-i,-o}(\sigma,r)\ge \eta/(8M).
\]

Distinct players' live-path behavioral randomizations induce independent
stopping laws. The full source opponent survival therefore factors exactly as

\[
 p(r)H_{-i,-o}(\sigma,r),
\]

giving `eta^2/(128M^2)`. At the receiving component `sigma[a]`, the owner
survives to `r` surely, so the paid row's live mass is the pair-deleted mass
and is at least `eta/(8M)`. This agrees with the division-free row estimate
`eta/4 <= 2M * liveMass`.

The Fin4 constants in (3.14) are all correct after choosing an outsider with
`J_i >= kappa/3`:

| quantity | lower bound |
| --- | ---: |
| paid gain | `kappa/12` |
| original owner survival | `kappa/(48M)` |
| original pair-deleted survival | `kappa/(24M)` |
| original full opponent survival | `kappa^2/(1152M^2)` |

For a sequence, the outsider identity must first be fixed by finite
pigeonhole, as the note says.

## 4. Fixed and escaping dates

Every natural-valued date sequence has a subsequence which is either constant
or tends to infinity. The fixed-date arm is stated correctly.

The escaping compactification is also correct, with one scope clarification:
the phrase “the three opponents of `i`” and formulas (4.1)--(4.2) are the
**Fin4 specialization** of Theorem 3.1. After compact extraction of the four
marginal stopping laws on `Nat union {Never}`, each fixed tail cylinder is
clopen. Hence for every fixed `N`, the lower bound at `r_n > N` passes to the
limit. Continuity from above then gives

\[
 \Pr(\text{all opponents of }i\text{ are Never})
 \ge \eta^2/(128M^2).
\]

Because the limiting law remains a product of the marginal limits, this is
the owner `Never` mass times the pair-deleted terminal survival of the other
two players. It does not imply a positive cemetery product at any finite
rank, nor continuity of caps, payoffs, minimum debt, or the retained atom.
The note is appropriately explicit about all of those nonclaims.

For an exact formal statement, (4.2) should identify which limiting root
sequence realizes `quittingPairDeletedSurvivalLimit`; the displayed
`PairDeletedSurvivalLimit` notation is currently informal.

## 5. Exact zero through the paid-cap lift

As a standalone statement, Corollary 3.2 is correct. If an actual profile
satisfies `d_o(sigma)=0`, then changing only `o` leaves `B_o` fixed and
prescribed payoff disintegrates affinely, so

\[
 \mathbb E_t d_o(\sigma[t])=d_o(\sigma)=0.
\]

Every summand is nonnegative on the countable clock space. Every
positive-mass component, including the selected `sigma[a]` and `sigma[b]`,
therefore has owner debt exactly zero.

It is also important, and correct, that the cap-lifted source be based at the
unmodified receiving component `sigma[a]`, not at the high outsider-response
endpoint. The `QuittingPaidCapLiftedSource` API accepts an arbitrary literal
profile carrying the row; the positive global minimum is a separate field.
At every exact cap-Nash prefix, the coordinate identity is

\[
 d_o(P_{h+1})=
 \operatorname{ContinueMass}(x_h)d_o(P_h).
\]

Thus exact zero persists through all finite literal prefixes. The semantic
port is the limit of these pairs, so continuity of the debt coordinate gives
zero owner debt at `port.semanticPort.limit`. The three predicates in
`exactTrichotomy` all refer to this same supplied port. There is no API loss
at this stage.

The reset-rigid application is different. In
`questions/FIN4_RESET_RIGID_CHAMBER_CONSUMER.md`, (R2) says `d_o(y)=0` for a
carrier point `y`. The common actual realizing sequence gives only

\[
 d_o(\sigma_n)\longrightarrow0.
\]

It need not have `d_o(sigma_n)=0` at any rank. Equation (3.16) then says only
that the average component owner debt tends to zero; it does not make every
positive-support component zero. The clocks selected by the rectangle
argument may lie on small atoms, so their debts cannot be declared zero by
the present proof. Accordingly these sentences must be revised:

- the final paragraph of Section 1;
- “under the reset-specific owner-zero premise” in Section 4; and
- the claimed rankwise old-owner-zero face in Sections 5 and 7.

They are valid under the stronger attained-profile hypothesis
`d_o(sigma_n)=0` for every rank, but that hypothesis is not supplied by the
reset-rigid chamber.

## 6. Quantitative repair for the actual reset sequence

There is a clean repair which retains the theorem's useful content. Put

\[
 \delta=d_o(\sigma)=\mathbb E_t d_o(\sigma[t]).
\]

Fix `L>0`. For independent `T,S`, Markov and a union bound give

\[
 \Pr(d_o(\sigma[T])>L\text{ or }d_o(\sigma[S])>L)
 \le 2\delta/L.
\]

Suppose there were no pair simultaneously satisfying

\[
 R\ge\eta/2,\qquad p(r)\ge\eta/(16M),\qquad
 d_o(\sigma[a]),d_o(\sigma[b])\le L.
\]

Using the same tail event as Theorem 3.1 and `|R| <= 4M` would give

\[
 \mathbb E R
 \le \eta/2+8M\frac{\eta}{16M}+8M\frac{\delta}{L}
 =\eta+8M\frac{\delta}{L}.
\]

This contradicts `E R >= 3eta/2` whenever

\[
 \delta/L<\eta/(16M).
\]

Along a reset-rigid realizing sequence with `delta_n -> 0`, take
`L_n=sqrt(delta_n)` when `delta_n>0`, using the exact-zero argument when
`delta_n=0`. Eventually the selected receiving and source clock components
have owner debt at most `L_n -> 0`, while **all constants (3.3)--(3.8) stay
unchanged**. Exact prefix scaling then keeps every finite-prefix owner debt at
most `L_n`, and the port limit also has owner debt at most `L_n`. Thus the
strongest reset-facing conclusion currently proved is:

> persistent positive Jensen loss yields source-visible fixed-gain paid ports
> whose old-owner debt vanishes across ranks, not ports which are identically
> on the owner-zero face at each rank.

This repaired sequence statement is the appropriate formalization target.
It still does not preserve the reset law, minimum fibre, marked atom, or other
old zero coordinates.

## 7. Regression audit

Section 6 is exact. The owner's displayed mixture can be realized behaviorally
by quitting at `n` with probability `1/2` and, conditional on survival,
quitting surely at `n+1`.

- With observer `i` prescribed `Never`, the actual outcome is always `{o}`
  and pays `i` zero.
- Any behavioral response of `i` wins only by matching the hidden owner date.
  Quitting at `n` with probability `x` and, after joint survival, at `n+1`
  yields success probability
  `(1/2)x+(1/2)(1-x)=1/2`; no later action helps. Hence `B_i=1/2` and
  `D(sigma_n)=1/2`.
- Conditional on either deterministic owner clock, matching it gives payoff
  one, so `J_i=1/2`.
- The two correct responses have rectangle `2`, first disagreement `n`, and
  all three stated finite-date survival probabilities equal one.

For the finite-splice boundary, every mover other than `i` has zero `Never`
mass. If the mover is `i`, deleting `i` and any one observer leaves two among
`o,a,b`, and both remaining clocks are almost surely finite. Thus every
pair-deleted terminal product is zero and so is its maximum. At either
deterministic response endpoint all four clocks are proper. After
`n -> infinity`, all four marginal laws converge to `Never`, and the product
jumps to one. The all-`Never` profile has total debt zero, so this is exactly
the claimed law-theoretic regression and not a positive-minimum
counterexample.

## 8. Narrow Lean declaration audit

The following checked declarations support the interfaces used here:

- `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`)
  confirms that the pure finite-time/`Never` menu has the same supremum as
  unrestricted behavioral deviations.
- The target note should additionally cite
  `quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime`
  (`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`),
  which is the exact arbitrary-observer deterministic-clock disintegration
  used in (2.4), (3.16), and the owner-law affinity step.
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` and
  `QuittingPaidFirstDisagreementRow.gain_le_liveMass`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`)
  accept the oriented receiving difference and retain both finite times and
  `Never`; the live-mass constant agrees with the note.
- `quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul`
  (`UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`)
  is the exact reached-row factorization.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`),
  together with `QuittingPaidCapLiftedSource.debt_antitone` and the
  `SummableSemanticPort.semantic_tendsto` field
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`),
  supports exact zero, or the repaired vanishing upper bound, through the
  cap-lifted port.
- `QuittingPaidCapLiftedSource.exactTrichotomy`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`)
  really dispatches that same port; it does not independently erase the
  owner coordinate.
- `quittingPairDeletedSurvivalLimit_eq_prod_neverMass`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteCapClock.lean`)
  and `exists_finiteSpliceCutoffs_tendsto_zero_of_capTight`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteSplice.lean`)
  confirm the distinction between a terminal cemetery product at one rank
  and a product appearing only after weak compactification across ranks.

The one-edge trace-friction estimate used for (3.12) remains ordinary
mathematics in
`CODEX_STRENGTHEN__CAP_SWITCHING_DELETED_BUBBLE_AND_REPLAY_CONTRACT.md`; I did
not find a named checked Lean declaration for that exact estimate. No Lean
declaration presently packages Theorem 3.1's tail quantile and rectangle
selection.

## 9. Export assessment

**No: this does not yet strictly narrow the reset-rigid question enough for
export.** After the repair, it is a useful and apparently new internal lemma:
it strengthens the earlier Jensen response square by retaining quantitative
owner-tail, pair-deleted, and full source survival, and it gives a sharp
moving-date regression. But it does not close or reduce (R1)--(R6) to a
strictly smaller consumed producer obligation:

- the exact owner-zero rankwise assertion currently overstates the actual
  reset adapter;
- the paid row still reaches the already known paid-cap trichotomy, whose
  literal inert arm is unconsumed;
- the fixed-date arm has no same-law/minimum-fibre return;
- the escaping atom exists only in a compact law limit and has no per-rank
  finite-splice or terminal consumer; and
- under a terminal exploitability gap, a generic full-gap paid row is already
  available at every literal profile, so the new survival floors require a
  named downstream use before they change the live frontier.

Accordingly the note should remain internal with verdict **REVISE**. The
concrete next question is whether the quantitative vanishing-owner repair can
be combined with reset-law/atom reprojection to rule out the inert port or to
produce an actual same-minimum return.
