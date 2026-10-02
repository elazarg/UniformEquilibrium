# Response-switch audit of the positive Jensen-curvature arm

Reviewer: `CODEX_RESPONSE_SWITCH`

## Verdict

The note's vanishing-Jensen branch is mathematically sound.  The complementary
positive-curvature branch does automatically contain a fixed two-pure-time
response switch, but current source-faithful response-switch machinery does
**not** consume it: the switch need not occur at a deterministic-clock
component which is simultaneously mass-good and near the positive global
minimum.

Thus the note identifies a genuine co-realization gap, not a missing
first-disagreement decoder.

## Exact pairwise switch hidden in Jensen curvature

Use the note's notation

\[
 \sigma=\sum_t\alpha_t\sigma^t,
 \qquad
 J_i=\sum_t\alpha_tB_i(\sigma^t)-B_i(\sigma)>0
\]

for one outsider `i != j`.  For every `t`, choose a pure time `q_t`, including
`Never`, whose payoff at `sigma^t` is within `epsilon` of the unrestricted
cap.  Write

\[
 V_t(q)=U_i(\sigma^t[i\leftarrow Q_q]).
\]

If `T,S` are independent with law `alpha`, fixed-response affinity in the
owner's stopping-law mixture gives

\[
 \mathbb E_{T,S}V_T(q_S)
 =\mathbb E_SV_\sigma(q_S)
 \le B_i(\sigma),
\]

whereas

\[
 \mathbb E_TV_T(q_T)
 \ge\sum_t\alpha_tB_i(\sigma^t)-\varepsilon.
\]

Therefore

\[
 \mathbb E_{T,S}[V_T(q_T)-V_T(q_S)]\ge J_i-\varepsilon,
\]

and some pair `s,t` satisfies

\[
 \boxed{V_t(q_t)-V_t(q_s)\ge J_i-\varepsilon.}
\]

The receiving target `sigma^t[i<-q_t]` has `i`-debt at most `epsilon`, and the
checked pure-time first-disagreement theorem retains the two named witnesses.
This strengthens the note's final paragraph: persistent Jensen loss already
produces an exact same-profile response-switch packet with a vanishing-debt
target coordinate.

## Why this still does not close the branch

Let

\[
 A=\{t:s_t\ge\mu/2\}.
\]

The note proves `alpha(A)>=mu/(2-mu)`, but the expected switch above may be
carried entirely by pairs whose receiving index `t` lies outside `A`.
Moreover

\[
 \sum_t\alpha_t(D(\sigma^t)-D_*)
 =D(\sigma)-D_*+J,
\]

so fixed positive Jensen curvature permits the switch-carrying component to
remain uniformly off the minimum fibre.  Neither its fixed response gain nor
its vanishing owner debt controls the other three unrestricted caps.

The reviewed source-faithful response-chord compiler requires precisely the
missing co-realization: an actual mass-carrying endpoint response whose joint
semantic/law limit is on the minimum fibre.  It cannot infer that input from
the pairwise switch alone.

## Precise follow-up

The positive-curvature branch would become consumable after any one of:

1. a weighted co-selection putting a fixed switch on `t in A` with
   `D(sigma^t)->D_*`;
2. a source-faithful reprojection of the switch target to the same minimum law
   while retaining its two response labels and marked row; or
3. a strict finite support/rank transition when all curvature-carrying
   components stay off minimum or mass-poor.

Returning only the pairwise switch above would be another paid-row output.
The missing content is the mass/minimum/source attachment.

