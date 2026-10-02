# Review of concrete nonlocality derivations, Items 1--2

**Reviewer:** `CODEX_RAMSEY` (review assignment `TESLA_COMPACT_EXCHANGE`)

**Source reviewed:**
`notes/CHATGPT_EXTERNAL__CONCRETE_NONLOCALITY_DERIVATIONS_INTAKE.md` and
Items 1--2 of `../idea_derivations.zip`, at the archive's stated/current head
`29a172f34a919f925bd1109a55c75c9a55d4078c`.

**Companion reviewed:**
`notes/CHATGPT_EXTERNAL__ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS_ACCOUNT.md`.

**Overall verdict:** Item 1 is mathematically **PASS with mandatory
provenance and subsequence qualifications**. Item 2 is **REVISE**, with the
core exchange identity, trichotomy, and constants passing; the repairs are
bounded and listed below. The companion social-surplus account is
mathematically **PASS after one scope wording repair**. None of these reviews
is an export gate.

I did not edit the supplied archive.

## Sources and declarations checked

I checked the compact stopping-law topology in
`MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`, unrestricted
pure-time extremality in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`, in
particular
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`, and the existing
compact-law implementation in
`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`.
The last file contains, among others,

- `quittingTerminalPayoff_update_compactStoppingLawProfile_finiteTime_tendsto`;
- `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit`;
- `QuittingOpponentTightLawSequence.of_twoProperLimits`;
- `quittingTerminalSemanticPair_eq_of_twoProper_lawLimits`; and
- `oneProper_minimum_negativeSingletonJump_of_notAttained_lawLimit`.

I also checked the first-disagreement identity in
`UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`.
The reviewed/formalized packet
`formalized/OPPONENT_TIGHT_TERMINAL_SEMANTIC_REALIZATION.md` already packages
the two-proper and one-proper realization boundary. I did not find the finite
coalition bubble coordinates or the moving-date exchange packet as checked
declarations in these named sources.

## Item 1: compact outcome bubble

### Verdict

**PASS as ordinary mathematics**, subject to the provenance wording below.

### Checks

1. Coordinatewise weak convergence of the finitely many compact stopping
   laws implies weak convergence of their finite product laws. For every
   nonempty coalition `S`, the outcome event `A_S` is open. Its closure is
   exactly
   \[
     \overline{A_S}=A_S\cup\{(\infty,\ldots,\infty)\}.
   \]
   The bounded-first-date/unbounded-first-date argument is exhaustive in the
   finite product of the one-point compactifications.

2. After one finite diagonal subsequence on the outcome probabilities,
   Portmanteau gives
   \(
     \delta_S=\lim_n p_n(S)-p(S)\ge0.
   \)
   Total mass gives the exact identity
   \[
     \sum_{S\ne\varnothing}\delta_S
       =p(\varnothing)-\lim_n p_n(\varnothing)
       \le p(\varnothing).
   \]
   Applying the closed-set inequality to
   `A_S union A_empty` also gives the claimed individual bound
   \(0\le\delta_S\le p(\varnothing)\).

3. The payoff formula is an exact finite moment identity:
   \[
     \lim_n U_n-U(\mu)=\sum_{S\ne\varnothing}\delta_S r(S).
   \]
   One proper limiting clock makes the product all-Never mass zero and hence
   kills all prescribed-payoff bubbles. This prescribed-payoff consequence
   agrees with, but is weaker than, the full opponent-tight realization
   interfaces already checked.

4. The prefix formula
   \(\delta'_S=h\delta_S\) is exact for a genuinely common literal prefix
   whose tail randomizations are fresh and whose conditional tail laws are
   the original product laws. Absorption before the splice cancels and the
   surviving branch has probability `h`.

### Mandatory qualification

The coordinates \(\delta_S\), and hence the normalized law `beta`, are
**subsequential defect masses**. They are not terminal-event masses of the
weak limiting profile and need not be the mass of any fixed finite-date atom.
What is source-native is the sequence of actual events: if
\(\delta_S>0\), then actual approximating profiles have terminal event `S`
with asymptotic probability at least \(\delta_S\). After a common prefix,
\(h\delta_S\) is again the relaxed defect coordinate; it is not by itself a
new fixed-date reached atom. The source should state this explicitly wherever
it calls the bubble an executable state or event.

The bubble can depend on the selected outcome-probability subsequence. If one
limiting clock is proper, each outcome event is a continuity set and the
zero-defect conclusion holds without a further outcome subsequence; this does
not make a nonzero general bubble canonical.

## Item 2: escaping cap exchange

### Verdict

**REVISE to PASS.** The pathwise identity, boundary estimate, exhaustive
subsequential alternatives, and quantitative constants are correct. Four
statement/provenance repairs are required.

### Exact algebra and topology

For a finite moving date `t_n`, the events in (2.1) partition
`{tau_n >= t_n}`. Coupling the finite-time deviation and Never on the same
opponent stopping vector gives exactly

\[
\begin{aligned}
 V_n(t_n)-V_n(\infty)
 ={}&\sum_A\alpha_{n,A}
       [r_i(A\cup\{i\})-r_i(A)]\\
 &+\sum_A\beta_{n,A}[r_i(\{i\})-r_i(A)]
   +\nu_n r_i(\{i\}).
\end{aligned}
\]

The time convention is correct: equality is collision, strict lateness is
solo preemption by `i`, and all opponents Never gives the singleton payoff.
Also
\(h_n=\Pr(\tau_n\ge t_n)\).

For fixed `T`, `{tau_n >= T}` is a clopen finite-tail event. Hence, when
`t_n -> infinity`,

\[
  \lim h_n\le\lim_{T\to\infty}\Pr(\tau\ge T)
     =\prod_{j\ne i}\mu_j(\{\infty\})=q_i.
\]

The displayed exchange limit is therefore valid after the stated finite
coordinate extraction.

### Cap trichotomy

The trichotomy of approximate pure maximizers is exhaustive, but the source
must first pass to a subsequence along which the bounded caps `B_n` converge
(or assume this, as happens in a semantically convergent source sequence).
Choose `epsilon_n`-maximizers and then pass to a further subsequence of
`Option Nat`: it is either one fixed finite date, Never, or finite dates
tending to infinity. The bubble/exchange packet may depend on both the cap
cluster and the chosen approximate-maximizer subsequence. Thus the unqualified
expressions `lim_n B_n` and “its entire defect” in Sections 4 and 7.2 require
this subsequential qualifier.

With that repair, formulas (4.1)--(4.2) are correct. Fixed finite values
converge by the named checked finite-time theorem; the Never value has the
opponent bubble; and the moving finite value is Never plus the exact exchange
premium.

### Quantitative constants

Assuming `L_i >= kappa > 0` and `|r_i(S)| <= M`, positivity forces `M>0` and
`h>0`. Positive exchange contributions have total mass at least
\(\kappa/(2M)\). There are

\[
  2(2^{|I|-1}-1)+1=2^{|I|}-1
\]

exchange types, so one has limiting mass at least

\[
  \frac{\kappa}{2M(2^{|I|}-1)}.
\]

Likewise the largest positive packet gap is at least
\(\kappa/h\ge\kappa/q_i\). For a full cap jump, adding the opponent-bubble
types gives the stated upper count
\(3(2^{|I|-1}-1)+1\). These constants check.

### Mandatory repairs

1. In Corollary 5.1, alternatives 1 and 2 must include their packet masses:
   respectively `alpha_A > 0` and `beta_A > 0`, in addition to a positive
   gap. The proof establishes this stronger statement; the present display
   does not connect its selected positive reward difference to the packet.

2. State `M > 0` in the quantitative corollary, or derive it immediately
   from `kappa > 0` and the reward bound before dividing by `M`.

3. The limiting `alpha_A`, `beta_A`, and `nu` are limits of **actual moving
   chronological events**, not atoms of the weak limiting law and not one
   fixed-date cylinder. Positive limiting mass yields an eventual actual
   mass floor (for example half the limit) along the selected subsequence.
   The provenance differs by type:

   - `alpha_A` is an actual date-`t_n` collision, changing terminal `A` to
     `A union {i}` under the deviation;
   - `beta_A` labels a future baseline coalition `A`, while under the
     finite-time deviation the terminal coalition is the singleton `{i}`;
   - `nu` also produces singleton `{i}` under the deviation.

   Thus `A` in a beta type is a chronological/counterfactual label, not a
   separate deviating-profile terminal atom. The phrase “quantitative
   terminal atom” is valid only with this distinction.

4. The opponent bubble coordinates in Section 6 are likewise defect masses,
   not atoms of the limiting law. They do imply actual event mass in the
   approximating profiles, but a positive `r_i(A)` bubble type is a positive
   payoff contribution, not by itself a profitable same-source deviation or
   a punishment-floor chronology. Section 9's final nonconsumer disclaimer
   is therefore essential.

### Overlap and surviving novelty

The unrestricted cap reduction to pure times, the two-proper full semantic
realization, and the one-proper residual classification already have checked
implementations in the sources named above. The exact collision--preemption
exchange identity and its moving-event mass extraction appear to be the new
part. They are a source-preserving decoder, not yet the reset/floor/Bellman
consumer suggested by the word “consumer.”

## Companion: all-player escape social-surplus account

### Verdict

**PASS after one wording repair.** This is a correct consequence of Item 1
and pure-time extremality.

For each fixed finite quit time, the deviation value is continuous in the
opponent laws. For the literal limiting opponent laws, as `t -> infinity`,

\[
  V_i(t)\longrightarrow V_i(\infty)
    +q_i r_i(\{i\}),
  \qquad q_i=\prod_{j\ne i}\mu_j(\{\infty\}).
\]

Hence nonnegative singleton rewards imply
\(\bar b_i\le\liminf_n B_i^n=b_i\). With
\(\Delta_i=b_i-\bar b_i\), the debt identity

\[
 D(\bar\sigma)-D(z)
   =\sum_{S\ne\varnothing}e(S)\sum_i r_i(S)-\sum_i\Delta_i
\]

has the correct sign. Global minimality yields the displayed surplus
inequality. If all nonempty coalition social rewards are nonpositive, the
weak limiting actual profile attains the same minimum **value**.

The mandatory wording repair is to replace “every positive global minimum is
attained” by “the positive global minimum value is attained by an actual
profile.” The proof need not realize every carrier point in the minimum
fiber.

The two-player boundary calculation also checks. If `c` is uniform on
`0,...,n` and `a` Never, then `a`'s pure-time values are
`1/(n+1)` at time zero, `(1-t)/(n+1)` for `1 <= t <= n`, and `-1` after the
support and at Never. Pure-time extremality gives the claimed cap. Any actual
profile with prescribed payoff `U_a=-1` must terminate at `{c}` almost
surely; at the least positive-support date of `c`, player `a` has a strictly
positive collision deviation. Thus the displayed semantic limit is not
attained, while all-Never is indeed a zero-debt actual profile.

This companion narrows all-player escape but does not prove the advertised
attainment-or-counterexample dichotomy. Its social-surplus special class is a
plausibly new narrow corollary relative to the named opponent-tight packet,
but it should be transcribed with the correction above and independently
reviewed as its own result before any export decision.

