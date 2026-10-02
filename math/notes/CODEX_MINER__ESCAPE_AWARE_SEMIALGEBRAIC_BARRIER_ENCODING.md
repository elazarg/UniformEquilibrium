# Escape-aware semialgebraic barrier encoding for `Fin 4`

Author: `CODEX_MINER`

Status: **complete sound certificate-language theorem and exact regressions;
internal, complementary to a stronger reviewed hierarchy.**  The
semantic soundness core is already checked in
`TerminalSemanticGlobalDebtBarrierCertificate.lean`.  The new contribution
here is an explicit finite rational/semialgebraic proof-object format and its
objective-direction audit.  No positive-floor certificate for a new reward
table and no hard-residual elimination is produced, so this note does not meet
the answer gate of
[`ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md).

After this note was written, the profile-dependent quantile construction in
[`CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md)
produced the stronger unconditional result: finite semialgebraic outer sets
with exact carrier intersection and certified bracket width `24/M`.  My
independent PASS review is
[`here`](../feedback/CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY__BY_CODEX_MINER.md).
The present invariant-barrier format remains a possible positive-gap proof
object but is not the primary escape-aware approximation theorem.

Review requested on the finite formulas, the unrestricted Bellman cap update,
the `delta/4` objective direction, and the scope of the fixed-menu no-go.

## 1. Question

Can one give a *finite and independently checkable* object which, if found for
a rational `Fin 4` reward table, proves a lower bound on exploitability against
every behavioral profile without truncating the escaping tail?

Yes, conditionally on finding an inductive semialgebraic barrier.  The
certificate below is finite, and its soundness is complete.  Search
completeness—whether every true positive gap has a barrier in any fixed
effective template—remains open.

## 2. Eight-dimensional semantic state and exact root action

Fix `I=Fin 4` and a rational reward table `r` with `|r_i(S)|<=1`.  A semantic
state is

\[
 z=(u,b)\in[-1,1]^4\times[-1,1]^4,
\]

where `u` is prescribed terminal payoff and `b` is the unrestricted
behavioral best-response envelope.

A one-stage behavioral root is represented by

\[
 p=(p_i)_{i\in I}\in[0,1]^4,
\]

where `p_i` is player `i`'s Quit probability.  For `S\subseteq I`, put

\[
 \pi_p(S)=\prod_{i\in S}p_i\prod_{j\notin S}(1-p_j),
 \qquad \alpha(p)=\pi_p(\varnothing).
\]

For a fixed observer `i`, and `T\subseteq I\setminus\{i\}`, put

\[
 \pi^i_p(T)=
 \prod_{j\in T}p_j
 \prod_{k\in I\setminus(T\cup\{i\})}(1-p_k),
 \qquad c_i(p)=\pi^i_p(\varnothing).
\]

Define the exact semantic prefix map `F_r(p,z)=(u',b')` by

\[
 u'_i=
 \sum_{\varnothing\ne S\subseteq I}\pi_p(S)r_i(S)
 +\alpha(p)u_i,                                      \tag{2.1}
\]

\[
 Q_i(p)=
 \sum_{T\subseteq I\setminus\{i\}}
   \pi^i_p(T)r_i(T\cup\{i\}),                       \tag{2.2}
\]

\[
 C_i(p,b)=
 \sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
   \pi^i_p(T)r_i(T)+c_i(p)b_i,                       \tag{2.3}
\]

and

\[
 b'_i=\max\{Q_i(p),C_i(p,b)\}.                      \tag{2.4}
\]

All expressions except the displayed maximum are rational polynomials.  The
graph of the maximum is the basic semialgebraic relation

\[
 b'_i\ge Q_i,quad b'_i\ge C_i,quad
 (b'_i-Q_i)(b'_i-C_i)=0.                             \tag{2.5}
\]

The formulas use the product-Bernoulli root itself.  Coalition probabilities
are not free simplex variables, so every boundary zero pattern and every
independence minor is automatically correct.

### Lemma 2.1: exact unrestricted cap recursion

If `z` is the semantic pair of an actual continuation profile and `p` is
prefixed as the first live root, then the resulting actual profile has
semantic pair `F_r(p,z)`.

**Proof.**  Equation (2.1) is the partition into a nonempty first-stage
quitting coalition and all Continue.  For a unilateral deviator `i`, choosing
Quit at the first root gives (2.2).  Choosing Continue gives the opponent-only
nonempty exits in (2.3), while on joint opponent continuation the deviator may
use an arbitrary tail behavioral strategy, whose supremum is exactly `b_i`.
Randomizing between Quit and Continue cannot exceed the larger endpoint and
can approximate either endpoint.  Thus the full behavioral envelope—not a
stationary or finite-horizon cap—is (2.4).  This is precisely the checked map
`quittingTerminalSemanticPrefix`.  ∎

## 3. Finite rational certificate object

Choose rational polynomials

\[
 g_1(z),\ldots,g_m(z)\in\mathbb Q[z_1,\ldots,z_8]
\]

and define the basic closed semialgebraic set

\[
 P=\{z\in[-1,1]^8:g_a(z)\ge0\text{ for }1\le a\le m\}. \tag{3.1}
\]

Let

\[
 z_\infty=
 \left(0,\bigl(\max\{0,r_i(\{i\})\}\bigr)_{i\in I}\right)             \tag{3.2}
\]

be the exact semantic pair of all-Never play.  A **rational semialgebraic
debt-barrier certificate of floor `delta`** consists of the finite data
`(delta,g_1,...,g_m)` together with exact proofs of the following rational
semialgebraic implications:

1. `delta>0` and `z_infty in P`;
2. for every `z in P` and every `p in [0,1]^4`,
   `F_r(p,z) in P`;
3. for every `z=(u,b) in P`,

   \[
   \delta\le\sum_{i\in I}(b_i-u_i).                 \tag{3.3}
   \]

The universal implications are finite first-order sentences over real closed
fields.  They may be discharged by exact quantifier elimination, rational
interval subdivision with complete algebraic endpoint certificates, or
Positivstellensatz/SOS identities whose rational polynomial expansions and
nonnegative multipliers are checked independently.  Floating-point sampling
does not count as a proof of an implication.

## 4. Soundness theorem

### Theorem 4.1

Every rational semialgebraic debt-barrier certificate of floor `delta`
defines a finite feasible relaxation satisfying the question's soundness
contract.  Namely take

\[
 R(r)=P,
 \qquad E(\sigma)=\operatorname{Sem}(\sigma),
 \qquad
 \Phi(u,b)=\frac14\sum_i(b_i-u_i).                  \tag{4.1}
\]

Then for every actual behavioral profile `sigma`,

\[
 E(\sigma)\in P,
 \qquad
 \Phi(E(\sigma))\le\operatorname{Expl}_r(\sigma),   \tag{4.2}
\]

and hence

\[
 \frac\delta4\le\inf_{z\in P}\Phi(z)
 \le\inf_\sigma\operatorname{Expl}_r(\sigma).      \tag{4.3}
\]

Thus a found certificate is a genuine counterexample certificate with
`gamma=delta/4` in the cap-supremum formulation.  If one wants an executable
deviation rather than the cap, any fixed `gamma<delta/4` is obtained by
approximating the relevant best-response supremum.

**Proof.**  Starting from (3.2), prefix invariance puts every finite root word
with an all-Never tail in `P`.  The checked theorem
`terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable` says
that the entire compact terminal-semantic carrier is the closure of precisely
these finite words.  The set `P` is closed, so it contains the carrier and in
particular every actual semantic pair.  Equivalently, the same conclusion is
the checked consumer `globalDebtFloor_of_certificate` after turning `P` and
conditions 1--3 into a
`TerminalSemanticGlobalDebtBarrierCertificate.Certificate`.

For an actual semantic pair every debt `b_i-u_i` is nonnegative and its
maximum is exactly profile exploitability.  The average of four nonnegative
numbers is at most their maximum, giving the second part of (4.2).  Condition
3 gives the first inequality in (4.3), and (4.2) gives the second.  ∎

This proves the lower-bound direction requested in the question.  In
particular, enlarging the actual semantic image to `P` is safe because the
objective is minimized on the larger set; a positive floor on the relaxation
therefore remains a floor on the actual image.

## 5. Audit of the six escape hazards

1. **Complete stopping laws.**  An arbitrary behavioral profile maps through
   its actual eight-coordinate semantic pair.  Its complete tail is not
   replaced by a bounded controller.

2. **Horizon escape.**  The certificate has no cutoff.  Prefix invariance is
   quantified over arbitrarily many iterations, while one finite proof checks
   the one-step inductive implication.

3. **Weak-limit mass transfer.**  The density theorem uses closure of finite
   elementary tails.  The proof needs only that the closed floor halfspace
   contains the limit; it never declares a positive-debt carrier limit to be
   an actual profile.

4. **All-Never and singleton preemption.**  The seed (3.2) retains the Never
   payoff zero and the exact singleton caps.  It is not replaced by the
   diagonal zero pair unless every own singleton reward is nonpositive.

5. **Product provenance.**  Each prefix is parameterized by four individual
   Quit probabilities.  Formulas (2.1)--(2.3) use their products, including
   deterministic faces.

6. **Unrestricted deviations.**  Equation (2.4) is the exact dynamic
   best-response envelope.  Its Continue endpoint passes the complete tail
   cap `b_i`, so late and history-dependent behavior is not omitted.

## 6. Exact zero-certificate companion

A finite root word `p_0,...,p_(N-1)` with rational coordinates is a finite
zero certificate when backward evaluation from `z_infty` yields a diagonal
pair `(u,u)`.  Lemma 2.1 then constructs a literal behavioral profile with
zero unrestricted terminal debt.  The checked terminal-to-uniform compiler
turns `u` into a uniform-equilibrium payoff.

As an exact nontrivial boundary test, take

\[
 r_i(S)=\begin{cases}1,&i\in S,\\0,&i\notin S.\end{cases}
\]

The Never seed has `u_i=0,b_i=1`.  Prefix the rational sure-joint root
`p_i=1` for all four players.  Equations (2.1)--(2.4) give

\[
 u'_i=1,\qquad Q_i=1,\qquad C_i=0,\qquad b'_i=1.
\]

Thus the one-root profile is an exact unrestricted terminal Nash profile and
produces the uniform payoff `(1,1,1,1)`.  This test is not a new special-case
theorem; it checks that the finite proof language's zero branch compiles to
the correct unrestricted semantic endpoint.

Approximate zero certificates may instead give, for every rational
`epsilon>0`, a finite rational word with maximum debt at most `epsilon` and a
convergent payoff subsequence.  The existing terminal-Nash-all-errors consumer
then supplies a uniform payoff.  A single finite word at one positive error is
not enough.

## 7. Fixed-menu impossibility inside this language

Let `F` be any finite set of deterministic quit dates and include Never.  Put

\[
 G_F(\sigma)=
 \max\left(0,
   \max_{i,\,t\in F\cup\{\infty\}}
      [U_i(\sigma[i\leftarrow Q_t])-U_i(\sigma)]\right).               \tag{7.1}
\]

### Proposition 7.1

Under a hypothetical global terminal gap, `inf_sigma G_F(sigma)=0` for every
finite `F`.  Consequently any proposed finite relaxation whose soundness proof
establishes only

\[
 \Phi(E(\sigma))\le G_F(\sigma)                     \tag{7.2}
\]

has `inf_R Phi<=0` and cannot certify a positive global gap.

**Proof.**  Choose a deadline strictly after every date in `F` and hazard-
realize a mixed Nash equilibrium of the finite planned-time game with that
deadline and Never.  Every deviation in (7.1) has nonpositive gain, so
`G_F=0`.  If `F` is empty, the deadline-zero/all-Never boundary suffices.
Applying (7.2) to this actual profile proves the claim.  ∎

This does not refute every finite-dimensional relaxation.  It isolates the
minimal failed implication: a tail variable is useful only if its proof
connects it to the full late-time cap, as (2.3)--(2.4) and all-root invariance
do.  Merely storing an unconstrained bubble scalar does not repair (7.2).

## 8. Diffuse-positive-debt regression

The checked two-player positive-debt nonattainment example has actual semantic
pairs converging to a positive-debt carrier point that no behavioral profile
realizes.  Theorem 4.1 remains sound on it: the closed barrier `P` must contain
the limit, but the map `E` is asserted only for actual profiles, and the floor
argument uses closedness rather than realization.  Conversely, a search
procedure may not extract an executable profile from an arbitrary feasible
point of `P`.  A **positive** barrier certificate needs no such extraction;
an alleged **zero** branch does and must supply a finite word or another named
actual chronology.

## 9. Exact relation to current checked work

The following inspected declarations already prove the semantic heart of this
note:

- `quittingTerminalSemanticPair_rootThenContinuation` and
  `quittingTerminalSemanticPrefix` give Lemma 2.1;
- `terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable` gives
  escape-complete density from the exact Never boundary;
- `TerminalSemanticGlobalDebtBarrierCertificate.Certificate`,
  `globalDebtFloor_of_certificate`,
  `behavioralDebtFloor_of_certificate`, and
  `not_exists_uniformEquilibriumPayoff_of_certificate` give the barrier
  adapter and semantic consumers; and
- `nonempty_certificate_iff_globalDebtFloor` gives logical completeness while
  explicitly warning that the carrier witness need not be an effective finite
  certificate.

These are in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean`
and its named imports.  The module documentation already observes that a
finitely described polynomial barrier would be semialgebraically checkable.
Therefore Theorem 4.1 is not claimed as a new semantic result.  Its narrower
value is the explicit `Fin 4` rational formula (2.1)--(2.5), the precise
relaxation objective (4.1), and the regression/no-extraction audit needed by
the algorithmic question.

The finite-deadline arbitrary-table producer and exact horizon-escape result
are consolidated separately in
[`CODEX_MINER__FINITE_DEADLINE_NASH_ESCAPE_CERTIFICATE_FORMALIZATION_PACKET.md`](CODEX_MINER__FINITE_DEADLINE_NASH_ESCAPE_CERTIFICATE_FORMALIZATION_PACKET.md).

## 10. Algorithmic boundary and next exact task

For fixed rational `r`, `delta`, and polynomial list `g`, validity of conditions
1--3 is decidable by real quantifier elimination.  Enumerating rational tables,
floors, and polynomial templates therefore gives a sound certificate search.
It is not known to terminate:

- a true positive gap admits the full semantic carrier as an abstract checked
  barrier, but no theorem gives it a finite semialgebraic presentation;
- failure to find a barrier at any bounded degree is not a zero-gap proof; and
- one finite approximate word is not a complete all-errors chronology.

The next conjecture-facing task is consequently one of the following, with no
intermediate diagnostic counted as closure:

1. find a rational `Fin 4` table and exact rational polynomial barrier with
   `delta>0`;
2. prove that the retained `PunishmentNormalResidualHardClass` or full Fin4
   hard residual admits no such positive barrier **and** extract a complete
   zero-debt chronology from that failure; or
3. prove a finite-template completeness theorem: every positive global floor
   has a barrier in a recursively enumerable template with a verified finite
   certificate, and pair it with a terminating zero branch.

Until one of these is done, the present result is a sound finite certificate
language and search substrate, not an answer to the main question.
