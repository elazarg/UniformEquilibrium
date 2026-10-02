# Delta and novelty audit of `CODIMENSION_ONE.md`

Reviewer: `CODEX_EULER`

## Verdict

**REVISE.**  The quantitative deletion inequality, reached-row constants,
suffix estimate, finite atom extraction, macroscopic-repair inequalities, and
five-player regression are mathematically sound.  The document nevertheless
mixes already reviewed mathematics with two genuinely new results and then
overstates the compact limit as five “full-gap source-matched exact face
roots.”

This audit is independent only for the new quiet-face atom/compactness and
macroscopic-repair material.  It is deliberately **not** an independent review
of my earlier sharp deletion theorem.

## Exact novelty split

### Already reviewed or duplicate

1. The deletion inequality

   \[
     \eta(r)\leq\max\{\eta(r^{-w}),\Gamma_w(r)^+\}
   \]

   is the `A=1` specialization of the sharp cap

   \[
     P+\min(1,A)(C-P)_+
   \]

   in
   `notes/CODEX_EULER__OPERATIONAL_ESSENTIALITY_SHARP_DELETION_PASSPORT.md`.
   The all-essential consequence `Gamma_w >= eta(r)` is therefore not new.

2. Exact finite pure-time extraction of an outsider gain, reached-source
   factorization, and the unweighted passport `max(P,C) >= gamma` were already
   audited in that note and in the operational-support note.  They should be
   cited as inputs, not presented as a new proof principle.

3. The Fin4 singleton/pair-base alignment and its source/provenance caveats
   are already in
   `notes/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`.
   `CODIMENSION_ONE.md` adds no new pair-base consumer, chronology, or rank
   decrease.

### Genuinely new ordinary mathematics

1. **Quantitative quiet-face reached atom without a solo-deficit
   hypothesis.**  From a deleted-game approximate Nash profile, the argument
   produces a finite reached suffix with a fixed reach floor, vanishing full
   survivor exploitability, and one fixed conditional coalition cell with a
   positive toggle and probability floor.  This is more general than the
   Fin4 theorem which assumes a separated solo premium and forces a
   nonsingleton join atom.

2. **Macroscopic outsider-repair no-go.**  If the outsider's replacement law
   has all-Continue ever-Quit mass `alpha`, survivor debt is at most
   `epsilon+4M alpha`; if the replacement is a `delta`-best reply, the
   outsider debt is at most `delta`.  Under an ambient positive gap this rules
   out an infinitesimal activation.  The additional identity using the
   unchanged outsider cap yields the sharper `2M alpha` lower bound.

3. The symmetric five-player table is a useful exact regression: five quiet
   lifts can each have a sole outsider debt one while the full game has an
   exact all-Quit equilibrium.  It refutes label-only combination, not the
   five-to-four implication.

## Quantitative audit

Fix `a=eta(r)>0`, `eta(r^{-w})=0`, and `0<gamma<a`.  Choose restricted
profiles with exploitability `epsilon_n -> 0`, and quietly lift them.

### Reached finite time and constants — PASS

For large `n`, all survivor debts are below `gamma`, while every ambient
profile has maximal debt at least `a`.  Hence the outsider debt exceeds
`gamma`.  The exact stopping-law expectation gives a finite pure time with
gain at least `gamma`.

Writing the gain as `rho_n Delta_n`, the reward bound gives
`|Delta_n| <= 2M`, and therefore

\[
  \rho_n\geq\frac\gamma{2M},\qquad \Delta_n\geq\gamma.
\]

This also proves `M>0`; division by `M` is not assumed before it is known.

### Suffix exploitability — PASS

A survivor deviation from the suffix can be spliced after the exact event
that all retained players survive before `t_n`.  The strategy agrees with the
source before that event, so its probability is precisely `rho_n`.  Thus

\[
  \operatorname{Expl}_{r^{-w}}(\theta_n)
    \leq\epsilon_n/\rho_n
    \leq(2M/\gamma)\epsilon_n.
\]

This is an unrestricted behavioral statement, not merely a one-row Nash
estimate.

### Coalition cell and absolute mass — PASS

There are sixteen cells `A subset J` in the five-player case.  Since

\[
  \sum_A p_n(A)g_n(A)\geq\gamma,
\]

the sum of the positive parts is at least `gamma`; hence some cell has

\[
  p_n(A)[g_n(A)]_+\geq\gamma/16.
\]

Every cell toggle is at most `2M`, so

\[
  p_n(A)\geq\frac\gamma{32M},\qquad
  g_n(A)\geq\frac\gamma{16}.
\]

Finite pigeonhole permits one fixed `A` on a subsequence.  Multiplying by the
reach floor gives the correct absolute mass

\[
  \rho_np_n(A)\geq\frac{\gamma^2}{64M^2}.
\]

For nonempty `A` this is a literal terminal atom of the quiet source at that
date.  For `A=empty` it is the singleton `{w}` only under the counterfactual
pure-time outsider deviation; the quiet profile itself does not absorb on
that cell.

### Compact limiting row — PASS with scope repair

Compactness of the finite product-root cube and bounded continuation-value
box gives a subsequential limit `(x^w,v^w)`.  The suffix exploitability bound
implies the limiting root satisfies the survivor one-stage endpoint-Nash
inequalities at `v^w`.  The immediate-Quit difference and fixed-cell bounds
are closed and survive.

What has **not** been shown is that `v^w` is attained by a behavioral suffix,
that `(x^w,v^w)` is an actual semantic pair, or that the five limits share a
source or chronology.  The safe conclusion is a **limiting local face-root
certificate obtained from actual reached suffixes**.

Also, for fixed `gamma<a`, its outward advantage is at least `gamma`, not the
full ambient gap `a`.  The phrase “five source-matched exact face roots, each
carrying a full-gap outward Quit direction” must be replaced by
“five limiting face-root certificates with arbitrarily subgap outward Quit
directions.”  Alternatively, add a separate diagonal argument
`gamma_m -> a` and retain the same finite cell along a subsequence; even then,
do not claim behavioral attainment without a closed-carrier proof.

## Macroscopic repair audit

Let `alpha` be the replacement outsider law's probability of ever quitting
on the all-Continue history.  Before the terminal action, every live history
is exactly such an all-Continue history.  Under a coupling of the replacement
profile and quiet profile, their terminal outcomes can differ only when that
clock is finite.  This remains true after any unilateral survivor deviation.
Therefore

\[
 |U_i(p)-U_i(q)|\leq2M\alpha,\qquad
 |B_i(p)-B_i(q)|\leq2M\alpha,
\]

and `d_i(p) <= epsilon+4M alpha` for every survivor.  This argument correctly
handles arbitrary behavioral deviations.

The outsider's opponents are unchanged, so its unrestricted cap is the same
at `p` and `q`.  If its replacement is `delta`-best, then `d_w(p)<=delta` and

\[
 U_w(p)-U_w(q)=d_w(q)-d_w(p).
\]

Consequently the two strict bounds

\[
 \alpha>\frac{\gamma-\epsilon}{4M},\qquad
 \alpha>\frac{\gamma-\delta}{2M}
\]

are correct under their respective displayed hypotheses.  When a numerator
is nonpositive the corresponding inequality is only vacuous, not false.

The document should define “`delta`-best response” explicitly as prescribed
payoff within `delta` of the unrestricted best-reply supremum.  Exact
best-response attainment is not required.

## Minor proof-writing repairs

1. In the `Gamma_w<0` deletion proof, an unreachable finite time has gain
   zero, not strictly negative.  Say every finite gain is **nonpositive**.
2. Replace “unique possible `gamma`-debtor” by “the only coordinate that can
   have debt at least `gamma`”; survivor debts need not be literally zero.
3. Distinguish conditional row mass `p_n(A)` from the source-weighted terminal
   mass `rho_n p_n(A)` everywhere.
4. State that the five quiet sources and their selected times may all differ.
5. The contemporary-literature sentence is unnecessary to the proof and is
   not a source correspondence.  If retained in an export packet, give the
   article title and exact theorem/open-problem statement rather than a bare
   Springer link and “uploaded provenance workflow.”

## Export and formalization recommendation

Do **not** export `CODIMENSION_ONE.md` as one packet.  It combines duplicate
material, two new local results, an open reduction, and a scope overstatement.

The appropriate formalization targets are two narrow declarations:

1. a quiet-face reached-atom theorem whose output keeps `rho`, the actual
   reached suffix, its unrestricted exploitability bound, the fixed cell, and
   the conditional and absolute mass constants separate; and
2. a macroscopic outsider-repair theorem parameterized by the all-Continue
   ever-Quit mass and an optional `delta`-best-reply hypothesis.

These belong in diagnostic/player-deletion or outsider-gluing infrastructure.
The sharp deletion cap should be formalized from its already reviewed owned
note, not credited as new to this document.

For conference export, the conservative verdict is **retain internally**
unless a named five-to-four question explicitly accepts quantitative
face-root/atom localization as a partial answer.  The new output supplies no
common executable source, no five-face gluing, no strict maintained rank
decrease, and no uniform-payoff consumer.  If that question does accept this
interface result, extract only the repaired reached-atom and macroscopic
repair theorems, with a separate whole-packet gate and the required reviews
for their unrestricted-strategy assertions.
