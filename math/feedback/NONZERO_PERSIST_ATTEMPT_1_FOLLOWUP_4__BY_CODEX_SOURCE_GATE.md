# Source/reach audit of `NONZERO_PERSIST_ATTEMPT_1`, Followup 4

**Reviewer:** `CODEX_SOURCE_GATE`  
**Verdict:** **FAIL for the claimed post-mark parent-reach producer and for
any nonzero parent-level paid splice; PASS for the pure-pair shield, the
standalone inner-profile debt argument, and the zero-debt-face minimum
theorem, subject to the scope corrections below**  
**Status:** ordinary-mathematics and narrow source/API audit; no Lean or
author-file changes

## 1. Claim audited

Followup 4 starts with equality-arm actualizer profiles

\[
 \sigma_n=A_n\triangleright q^S\triangleright R_n,
 \qquad |S|=2,
\]

and defines the self-replayed parent

\[
 \pi_n=A_n\triangleright q^S\triangleright\sigma_n.    \tag{1}
\]

It then regards the occurrence of the same pair row inside the restarted
copy of \(\sigma_n\) as a uniformly reached post-mark two-cut block.  The
key question is whether the reach field is a reach in the whole parent
\(\pi_n\), as required for a parent-level paid/debt splice, or only a reach
measured after entering the counterfactual post-mark tail port.

The distinction is fatal here.  The outer root \(q^S\) has joint Continue
probability zero.

## 2. Exact absolute-reach calculation

Let \(L_n\) be the probability that \(\pi_n\) reaches its outer marked row
at date \(m_n\).  The checked marked-mass floor gives \(L_n\ge\rho>0\).
But

\[
 c(q^S)=\Pr_{q^S}(\hbox{all Continue})=0.              \tag{2}
\]

The inner copy's entry cut is local date \(m_n\) in \(\sigma_n\), hence
absolute date \(2m_n+1\) in \(\pi_n\).  Literal multiplication of reach
therefore gives

\[
 \Pr_{\pi_n}(\hbox{reach }2m_n+1)
 =L_n\,c(q^S)\,
   \Pr_{\sigma_n}(\hbox{reach }m_n)
 =0.                                                   \tag{3}
\]

Consequently the inner pure-pair row has:

- local root hazard \(\sum_iq_i=2\);
- local reach at least \(\rho\), **conditional on starting the tail port
  \(\sigma_n\)**; but
- absolute parent reach, unconditional stage mass, and absolute absorption
  contribution all equal to zero.

This is not a small-loss issue.  It is exact nullity at every rank.

The card-two screen also makes (3) robust to unilateral behavior.  If one
member of \(S\) changes strategy, the other still Quits surely at the outer
row; if an outsider changes strategy, both members still Quit.  Thus no
one-player deviation which agrees before the proposed inner splice can open
the inner block.

## 3. Spec verdict for the two-cut object

There are two possible specifications, and Followup 4 must choose one.

### 3.1 Parent-reach specification

If `HasUniformlyReachedPostMarkTwoCutBlock` requires

\[
 \Pr_{\operatorname{parent}_n}
   (\hbox{reach the absolute entry cut})\ge r>0,        \tag{4}
\]

then the construction **does not inhabit the specification**.  Equation
(3) directly contradicts (4).  The boxed implications (24) and (51) in the
author file are false under this reading.

### 3.2 Two-port relative-reach specification

If the structure instead stores

\[
 \Pr_{\operatorname{postMarkTail}_n}
   (\hbox{reach the local entry cut})\ge r>0,           \tag{5}
\]

then the displayed fields are internally correct: the spine after the outer
mark is literally \(\sigma_n\), and the second pair row is reached inside
that standalone port with probability at least \(\rho\).

But (5) is a **counterfactual two-port field**, not parent reach.  It cannot
be fed to any theorem whose gain or debt is multiplied by reach from the
whole parent.  The object must be named and documented accordingly.  In
particular, its local hazard \(2\) is not an absolute charged block in the
parent chronology.

This is precisely the constant-extension phenomenon proved in
`notes/CODEX_ADVERSARY__PURE_PAIR_SCREENED_TWO_PORT_CAUSAL_TRANSPORT_NOGO.md`:
the whole upstream semantic pair and law are independent of the installed
tail, and the downstream fibre is unobservable from the parent.

## 4. The paid splice has no nonzero absolute gain

Followup 3's parent-level gain formula explicitly assumes that the original
parent reaches \(C_1\) with probability \(r_0>0\).  Applied to (1), that
hypothesis has \(r_0=0\).  Hence the correct lower bound is zero, not
\(r_0K_\chi/16>0\).

More directly, let \(\tau_n\) be any profile obtained by changing one
player's behavior only inside the restarted copy of \(\sigma_n\), and set

\[
 \widehat\tau_n
 =A_n\triangleright q^S\triangleright\tau_n.
\]

Complete pure-pair screening gives the exact equality

\[
 U(\widehat\tau_n)=U(\pi_n),\qquad
 B(\widehat\tau_n)=B(\pi_n),                           \tag{6}
\]

and equality of their terminal laws.  Thus the parent-level payoff gain and
every parent-level debt change are exactly zero.

There is a genuine positive gain available in the standalone profile
\(\sigma_n\), but it cannot simultaneously preserve the preceding replay
mark:

- Work in \(\sigma_n\): its own pair row is reached with mass at least
  \(\rho\), so the local deviation has positive absolute gain, but the
  deviation occurs at that marked row (and a complete best response can
  change behavior even earlier).  It does not retain that row as a strictly
  preceding source mark.
- Reattach the changed tail behind the outer pair in \(\pi_n\): the outer
  atom is retained exactly, but the gain is screened to zero by (6).

The construction therefore proves a two-port coexistence, not a causal paid
splice transporting a nonzero gain past the retained mark.

## 5. Section 1: pure nonsingleton shielding

**PASS.**  Equations (1)--(5) of Followup 4 are correct for
\(|S|\ge2\).  A unilateral deviator cannot remove every sure quitter, so the
prescribed payoff, unrestricted cap, and complete outcome law are independent
of the installed continuation.  The relevant checked theorem is
`quittingTerminalSemanticPair_literalRootStack_pureSet_screen` in
`UniformEquilibrium/Quitting/Paths/PureNonsingletonCommonPrefixScreening.lean`;
the literal tail and marked-mass identities are in the self-tail/cross-tail
modules named in the author file.

This result supports the negative conclusion (3), not a positive causal
transport claim.  “Source preservation” here means that the upstream
observation is constant in the tail.

## 6. Section 2: replay construction

**PASS as a literal null-branch factorization; FAIL as the advertised
parent-reached producer.**

The identities

\[
 \pi_n=A_n\triangleright q^S\triangleright\sigma_n,
 \qquad
 \operatorname{Spine}(\pi_n,m_n+1)=\sigma_n
\]

are correct, as are semantic/law preservation and the outer marked-atom
floor.  The second copy is a real component of the behavioral-strategy
record.  It is nevertheless situated entirely behind a probability-zero
history.  The words “same-witness chronology” are acceptable only if
qualified as a counterfactual extension chronology; “uniformly reached
parent block” is not.

Equations (20)--(21) in the author file mix the two measures.  Equation (20)
is reach under \(\sigma_n\); the claimed parent is \(\pi_n\).  Equation (21)
is conditional root hazard, not absolute block mass.  These facts cannot be
combined into a positive parent-level charge.

## 7. Section 3: standalone inner-profile debt and support handoff

The central ordinary mathematics in Section 3 survives, but it does not use
self-replay.

### 7.1 Valid local argument

View \(\sigma_n\) as a standalone actual profile.  At its reached pure-pair
row, let \(Z_n\) be the semantic pair of the suffix beginning at that row.
Then

\[
 D(Z_n)\ge D_*,
\]

and pure nonsingleton screening identifies its four debt coordinates with
the four one-row best-endpoint defects.  Hence some \(p_n\) has defect at
least \(D_*/4\), and the literal live-mass identity gives an actual
same-row deviation gain at least

\[
 \rho D_*/4.                                          \tag{7}
\]

Finite-label extraction fixes one player \(p\).  Approximate best response
against the same opponents then gives target profiles with
\(d_p\to0\).  The minimum-endpoint half-mixture calculation and strict
support inclusion are valid ordinary mathematics.

### 7.2 Scope and duplication

This argument is independent of (1): it is a theorem about \(\sigma_n\)
itself.  For the support-handoff purpose it is also unnecessary.  Since
\(D(\sigma_n)\to D_*>0\), simple four-coordinate averaging already selects a
fixed player with asymptotic debt at least \(D_*/4\), without the pair row or
the factor \(\rho\).  This stronger direct reduction is proved in
`notes/CODEX_ADVERSARY__FIN4_POSTMARK_DIRECT_DEBT_HANDOFF.md`.

The pair-row proof remains useful as a same-row provenance statement, but
that provenance is lost when one asks simultaneously for the replayed outer
mark and positive parent gain.

### 7.3 Checked-status correction

The named checked theorem
`exists_minimumEndpointSupportRankHandoff_or_debtAscent` in
`Research/Quitting/StoppingLawMinimumEndpointSupportRankHandoff.lean`
assumes

\[
 d_p(\tau_n)=0\quad\text{for every }n.                 \tag{8}
\]

Followup 4 constructs only \(d_p(\tau_n)\le\varepsilon_n\to0\), because an
unrestricted behavioral best-response supremum need not be attained.  The
asymptotic-zero extension is mathematically sound by continuity, and it is
spelled out in
`notes/CODEX_SOURCE_GATE__FOLLOWUP3_RENEWABLE_CHILD_ADAPTER.md`, but it is
not the named checked declaration.  The phrase “exactly the checked
support-rank handoff” must therefore be changed to “the ordinary
asymptotic-zero extension of the checked handoff.”

The later complete same-residual source regeneration and renewable trace are
also an ordinary assembly of checked components, not a conclusion of the
handoff declaration alone.  They survive with the exact scope recorded in
that adapter: source-independent terminal conclusions compile backward; the
incoming marked atom and parent-local deviation data do not.

## 8. Section 4: zero-debt-face relative minimum

### 8.1 Mathematical theorem

**PASS.**  If

\[
 \mathcal F_p=\{z:d_p(z)=0\}
\]

is nonempty and \(Z_p\) minimizes total debt on it, exact cap--Nash prefix
scaling gives

\[
 d_i(T_xZ_p)=c(x)d_i(Z_p).
\]

The prefix remains in \(\mathcal F_p\), so positive minimum debt forces
\(c(x)=1\).  Every exact root is therefore all Continue, and Nash existence
makes it the unique exact root.  The same proof works after setting any
fixed collection of debt coordinates to zero.

This is not new relative to the current checked API.  The one-coordinate
case is already
`exists_resetFace_minimizer_with_unique_allContinue_capNash` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetExcursionReturn.lean`.
Followup 4 gives a clean rederivation and the evident multi-coordinate
variant.

### 8.2 Source attachment

Installing realizers \(\zeta_k\to Z_p\) behind the outer pure pair is a
literal strategy construction, and it preserves the upstream semantic/law
point.  But it does so precisely because the installed tail has zero
absolute reach.  The resulting passport is

\[
 \{Z_p\}\times\{z_{\rm upstream}\}
\]

inside the product two-port passport, with no nonzero transport coefficient.
It does not show that the downstream plateau inherits the upstream atom,
payoff gain, or debt change.  Calling it “source-attached” is acceptable only
with this null-port qualification.

Thus Section 4 can replace the off-minimum positive-root discussion by the
canonical relative plateau as a **downstream classification**.  It does not
consume that plateau and does not repair the failed paid splice.

## 9. Required repairs to Followup 4

1. Replace the boxed implications (24) and (51) by a specification fork:
   either mark them **FAIL** for absolute parent reach, or rename the output
   as a relative-reach counterfactual two-port block.
2. After (20), display the absolute calculation (3).  State that the inner
   row's unconditional parent stage mass is zero.
3. Do not call the hazard \(2\) a parent charge.  It is the conditional sum
   of marginal hazards at the local tail port.
4. Remove every suggestion that a post-inner-cut deviation has a nonzero
   payoff gain in \(\pi_n\).  Equation (6) gives exact zero.
5. State Section 3 directly for the standalone \(\sigma_n\).  Make explicit
   that its positive same-row deviation does not preserve a strictly earlier
   replay mark.
6. Qualify the handoff as ordinary mathematics extending the pointwise-zero
   checked theorem, and cite the separate regeneration adapter for the
   renewable conclusion.
7. Present Section 4 as the already-checked reset-face minimum theorem (plus
   a routine multiple-zero-coordinate extension) and qualify its reattachment
   as a null-branch product passport.

## 10. Final packet-level verdict

The self-tail replay does **not** close the missing chronological adapter in
the parent-reach sense.  It manufactures a second charged-looking row only
behind a sure-absorption screen.  Relative to the replayed tail that row is
reached; relative to the claimed parent it has reach zero, absolute charge
zero, and paid-splice gain zero.

Two pieces of mathematics remain valid independently:

1. the standalone equality actualizer profiles admit a fixed positive-debt
   player and hence the ordinary minimum-support-child versus off-minimum
   zero-debt handoff; and
2. every nonempty killed-debt face has a total-debt minimizer whose exact cap
   root is uniquely all Continue.

The first is already obtainable more directly from
\(D(\sigma_n)\to D_*>0\); the second is already present in the checked
reset-face API.  Neither supplies a nonzero causal edge connecting the
retained upstream atom to the downstream child.  The original blocker
therefore survives unchanged: one needs a permeable marked row with positive
post-mark transmission, a genuinely renewed reached row inside the actual
post-mark continuation, or a consumer explicitly designed for two causally
disconnected ports.

