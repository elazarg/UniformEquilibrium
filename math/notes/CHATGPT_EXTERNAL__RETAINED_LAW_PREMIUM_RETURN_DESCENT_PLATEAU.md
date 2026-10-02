# Retained-law premium: return, descent, or plateau

**Identity:** `CHATGPT_EXTERNAL`

**Source:** `../RETAINED_PREMIUM.md`, supplied directly by the user on
2026-08-26.

**Status:** `INDEPENDENTLY REVIEWED WITH A CONDITIONAL CORE`; ordinary
mathematics, not Lean-checked; no part currently passes the export gate.

Independent review and export audit:

-
  [`feedback/CHATGPT_EXTERNAL__RETAINED_LAW_PREMIUM_RETURN_DESCENT_PLATEAU__BY_JAMES.md`](../feedback/CHATGPT_EXTERNAL__RETAINED_LAW_PREMIUM_RETURN_DESCENT_PLATEAU__BY_JAMES.md)
-
  [`feedback/CONCRETE_NONLOCALITY_DERIVATIONS_EXPORT_GATE__BY_HOOKE.md`](../feedback/CONCRETE_NONLOCALITY_DERIVATIONS_EXPORT_GATE__BY_HOOKE.md)

Candidates A and B pass after exposing the fixed-law `IsMinOn` proof and
stating the law metric, triangle term, and source-side exactness. Candidate C
passes as a conditional outer-sequence return consumer. The final plateau
claim does not pass: the rigorous complement is only absence of a lower-region
entrance, not yet a unique-all-Continue/delayed-support theorem. Moreover the
live near-minimum cap sources have absorption tending to zero, so Candidate
C's fixed positive-absorption premise is not presently produced there.

## Question

In the strict fixed-law/global reset-face premium branch, what does the
positive premium force on an actual chronology that retains the literal
rectangle suffix?  Can it produce a cumulative payoff return, or does it only
produce descent and an inert residual?

## Existing checked input

Let

\[
 \delta=D(\texttt{bridge.fixed})-D(\texttt{bridge.global.1})>0
\]

and let `mu` be the retained endpoint law.  The checked declaration
`QuittingStoppingLawRectangleMinimizerBridge.eventually_literal_lawPremium`
keeps the literal double-endpoint profiles and the rectangle atom while
eventually proving

\[
 \delta/2 < D(x_n)-D(\texttt{bridge.global.1}).
 \tag{1}
\]

This is a retained-law premium, not by itself chronological charge or payoff
return.

## Candidate A: strict-law separation

The intended strengthened bridge retains the fact that `bridge.fixed` is a
minimum of total debt among joint semantic/law points having observer debt
zero and law exactly `mu`.  Under that strengthened field, compactness gives
constants `rho>0` and `epsilon0>0` such that every joint carrier point `z`
with

\[
 d_o(z.1)\le\varepsilon_0,
 \qquad
 D(z.1)\le D(\texttt{bridge.global.1})+\delta/2
 \tag{2}
\]

satisfies

\[
 \operatorname{dist}(z.2,\mu)\ge\rho.
 \tag{3}
\]

Otherwise a compact limit would have exact observer reset, law `mu`, and
debt at most `D(global)+delta/2`, contradicting fixed-law minimality.

### Required interface correction

The current structure `QuittingFixedLawResetDispatch` retains `joint`,
`reset`, `source_le`, `target_ge`, transfer/toggle data, and a dynamic exit.
It does **not** retain the universal fixed-law minimality statement.  The
underlying theorem `exists_fixedLaw_resetFace_minimizer` does select a true
fixed-law minimizer, but the wrapper drops its `IsMinOn` content.

Therefore (3) is mathematically available after strengthening the dependent
bridge or reconstructing the minimizer with its proof; it is not justified by
the present public field `bridge.fixed_dispatch` alone.

## Candidate B: charge of every actual lower-face entrance

Prefix the same exact cap-Nash stack to the literal rectangle endpoints.  If
`s_h` is joint survival and `q_t` the root absorption charges, then on the
cap-lifted source side

\[
 D(\widehat x_{n,h})=s_hD(x_n),
 \qquad
 d_o(\widehat x_{n,h})=s_hd_o(x_n).
 \tag{4}
\]

The terminal law of a literal prefix differs from its suffix law by at most
`1-s_h`, while

\[
 1-s_h\le\sum_{t<h}q_t.
\]

Combining law convergence of `x_n` to `mu` with (3), any late actual prefix
entering

\[
 D(\widehat x_{n,h})
 \le D(\texttt{bridge.global.1})+\delta/2
\]

must satisfy a uniform cumulative-charge lower bound

\[
 \rho/2\le\sum_{t<h}q_t.
 \tag{5}
\]

Global positive minimum also bounds `s_h` away from zero, so the literal
rectangle atom retains a fixed positive fraction.  This is a conditional
coercivity theorem: it does not produce the entrance.

The formal statement must specify the law metric (or use the current finite
simplex metric) and include the triangle term between the law of `x_n` and
`mu`.

## Candidate C: asymptotic cap-return consumer

Let `source n` be actual-profile paid cap sources and `port n` summable ports.
Write `A_n` for total absorption and `c_n` for cap displacement between source
and port.  If some `a>0` satisfies

\[
 A_n\ge a\quad\text{eventually},
 \qquad c_n\to0,
\]

then there is a
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` with charge floor
`a/2`.

For a requested endpoint error, first choose `n` with `A_n>=a` and source-to-
port displacement below half the error.  Then choose a finite cap-prefix
depth whose accumulated charge is at least `a/2` and whose value is within
half the error of the port.  The triangle inequality closes the seam.  Each
returned finite path lies wholly in one source's exact punishment-floor cap
chronology, so varying `n` creates no source splice.

This is an outer-sequence version of the checked fixed-source
`nonempty_cumulativeNearReturnFamily_of_totalAbsorption_pos_of_capDisplacement_zero`
argument and appears to be a clean Research formalization target.

## Conditional rectangle reduction

Apply actual-profile paid cap ports to the late literal endpoints `x_n`.  If
their port limits enter the lower half of the reset face, Candidate A/B forces
their total absorption to have a positive liminf.  Then:

1. cap displacement tending to zero gives the cumulative near-return family
   by Candidate C, hence a checked uniform-payoff consumer;
2. cap displacement bounded below gives a uniform semantic-debt descent by
   the checked quantitative cap-port branch, approximable at finite literal
   prefixes that retain the suffix and atom;
3. failure to enter leaves only the no-lower-region-entrance complement.

The second branch still needs regeneration or a finite well-founded rank. The
third item must not be strengthened to a unique-all-Continue or delayed-entry
plateau without another theorem; it still has the prescribed-payoff/cap
mismatch and is not consumed by the retained atom or paid row alone.

## Boundary and nonclaim

The strict premium does not itself prove positive charge.  It proves charge
for any actual causal entrance into a separated lower region.  Existence of
such an entrance remains open.  The final proposed plateau description also
needs a precise quantified theorem; it should not be exported as an exhaustive
result merely from the informal maximal-root discussion.

## Review request

Check:

1. the exact missing minimality field and the narrowest repaired bridge;
2. compact separation in the joint semantic/law carrier;
3. the law-distance versus prefix-absorption estimate;
4. the outer-sequence quantifier order and charge floor in Candidate C; and
5. which part of the final return/descent/plateau reduction is already checked
   versus conditional on an entrance.
