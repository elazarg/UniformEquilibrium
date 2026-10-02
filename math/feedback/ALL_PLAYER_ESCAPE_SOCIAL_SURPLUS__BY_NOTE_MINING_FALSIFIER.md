# Gate review: all-player escape social-surplus account

**Reviewer:** `CODEX_GATE_FALSIFIER`

**Source reviewed:**
[`notes/CHATGPT_EXTERNAL__ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS_ACCOUNT.md`](../notes/CHATGPT_EXTERNAL__ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS_ACCOUNT.md)

**Verdict:** **MATHEMATICAL PASS; CURRENT EXPORT PACKET REVISE.**  I found no
counterexample to the escape-mass sign, cap lower semicontinuity, debt-jump
identity, or attainment conclusion.  The strongest theorem is slightly
stronger than the note states: positivity of the minimum value is unnecessary
for the sign-chamber attainment conclusion.  The note is not yet an
export-ready packet because it abbreviates the bubble proof, does not spell out
the carrier-to-law-limit adapter, has no negative test showing why the
singleton sign is needed, and does not attach the attained profile to a named
downstream consumer.  These are bounded packaging/proof-completeness repairs,
not a mathematical defect.

I attempted to falsify the theorem by varying the escaping clock, allowing
Never mass in only some coordinates, allowing one proper limiting clock, and
making finite-time maximizers run to infinity.  The only failure found is the
expected one when an own singleton reward is negative; an exact two-player
counterexample is given below.

## Exact strongest surviving theorem

Let (I) be a nonempty finite player set and let (r(S)\in\mathbb R^I) be a
finite quitting reward table for every nonempty coalition (S\subseteq I),
with all-Never payoff zero.  Let 

\[
  \operatorname{Sem}(\sigma_n)=(U^n,B^n)\longrightarrow z=(u,b)
\]

for actual behavioral profiles (\sigma_n).  After passage to a common
subsequence, suppose every induced stopping law converges weakly on
(\overline{\mathbb N}=\mathbb N\cup\{\infty\}) to a law (\mu_i), and the
finite terminal-outcome masses converge coordinatewise to (m^*).  Let
(\bar\sigma) be the actual behavioral profile reconstructed from the product
law (\bigotimes_i\mu_i), let (m) be its complete terminal-outcome law, and
write

\[
  e(S)=m^*(S)-m(S)\qquad(S\ne\varnothing).
\]

Then:

1. (e(S)\ge0) for every nonempty (S).
2. For every player (i),
   \[
     u_i-U_i(\bar\sigma)=\sum_{S\ne\varnothing}e(S)r_i(S).
   \]
3. If (r_i(\{i\})\ge0) for every (i), then
   \[
     B_i(\bar\sigma)\le b_i.
   \]
   With (\Delta_i=b_i-B_i(\bar\sigma)\ge0) and
   (R(S)=\sum_i r_i(S)),
   \[
     D(\bar\sigma)-D(z)
       =\sum_{S\ne\varnothing}e(S)R(S)-\sum_i\Delta_i. \tag{A}
   \]
4. If (z) is a global minimizer of (D) on the terminal-semantic carrier,
   then
   \[
     \sum_Se(S)R(S)\ge\sum_i\Delta_i\ge0. \tag{B}
   \]
   If no actual behavioral profile has debt equal to that carrier minimum
   value, the first inequality is strict.
5. Consequently, under
   \[
     r_i(\{i\})\ge0\quad\text{for all }i,
     \qquad R(S)\le0\quad\text{for all nonempty }S, \tag{C}
   \]
   the global carrier minimum **value** is achieved by an actual behavioral
   profile.  This conclusion holds whether the minimum value is positive or
   zero.  It does not assert that every carrier point on the minimum fibre is
   realized.

The last conclusion follows for an arbitrary carrier minimizer because the
existing selected-law-limit construction supplies the required realizing
sequence and a common weak-law subsequence; the finite outcome simplex supplies
the further outcome-law subsequence.

## Audit of the escape-mass sign

Fix a nonempty coalition (S) and a finite horizon (T).  The probability
that the first terminal coalition is (S) at some date at most (T) is a
finite polynomial in the stopping-law point masses at dates (0,\ldots,T).
Those finite singleton coordinates converge under weak convergence on the
one-point compactification.  Therefore

\[
 \Pr_{\bar\sigma}(S\text{ occurs by }T)
   =\lim_n\Pr_{\sigma_n}(S\text{ occurs by }T).
\]

Since the finite-horizon event is contained in the complete (S)-outcome
event,

\[
 \Pr_{\bar\sigma}(S\text{ occurs by }T)
   \le \liminf_n m_n(S)=m^*(S).
\]

Monotone convergence as (T\to\infty) gives (m(S)\le m^*(S)).  Thus
(e(S)\ge0).  Equivalently, the exact-(S) outcome event is open in the finite
product of the one-point compactifications, so the same conclusion follows
from Portmanteau.  No terminal atom at a fixed date is being asserted: (e(S))
is a subsequential compactification defect coordinate.

The complete laws lie in a finite simplex, so total mass also gives

\[
  \sum_{S\ne\varnothing}e(S)=m(\mathrm{Never})-m^*(\mathrm{Never})\ge0.
\]

This is the precise sense in which finite terminal mass is transferred to the
all-Never outcome of the reconstructed limiting profile.

## Prescribed payoff and cap audit

The all-Never outcome pays zero.  Since there are only finitely many terminal
coalitions,

\[
 u_i=\sum_{S\ne\varnothing}m^*(S)r_i(S),\qquad
 U_i(\bar\sigma)=\sum_{S\ne\varnothing}m(S)r_i(S),
\]

which proves the escaped reward-moment identity.

For the cap, fix a player (i).  Pure-time extremality is exact for the full
unilateral behavioral class:

\[
 B_i(\sigma)=\sup_{t\in\mathbb N\cup\{\infty\}}V_i(t;\sigma_{-i}).
\]

For each fixed finite (t), weak convergence of the opponent laws gives

\[
 V_i(t;(\sigma_n)_{-i})\longrightarrow
 V_i(t;\bar\sigma_{-i}).
\]

Against the limiting opponent laws, direct event decomposition gives

\[
 \lim_{t\to\infty}V_i(t;\bar\sigma_{-i})
 =V_i(\infty;\bar\sigma_{-i})
  +q_i r_i(\{i\}),
 \qquad
 q_i=\Pr_{\bar\sigma_{-i}}(T_j=\infty\ \forall j\ne i).
\]

If some opponent is proper then (q_i=0) and opponent absorption makes the
difference vanish.  If every opponent has positive Never mass, the only extra
limiting event is that they all Never, on which finite late quitting pays the
singleton reward.  Hence (r_i(\{i\})\ge0) makes Never weakly dominated in the
supremum by sufficiently late finite quit times.  It follows that

\[
\begin{aligned}
 B_i(\bar\sigma)
 &=\sup_{t\in\mathbb N}V_i(t;\bar\sigma_{-i})\\
 &=\sup_{t\in\mathbb N}\lim_nV_i(t;(\sigma_n)_{-i})\\
 &\le\liminf_n\sup_{t\in\mathbb N}V_i(t;(\sigma_n)_{-i})\\
 &\le\liminf_nB_i(\sigma_n)=b_i.
\end{aligned}
\]

This direction is correct.  It is lower semicontinuity of the cap as a
function of the opponent law tuple: the cap at the limiting actual profile is
no greater than the limiting semantic cap because the latter may retain an
escaping moving-date premium.

## Debt identity and minimum consequence

Subtraction is exact:

\[
\begin{aligned}
D(\bar\sigma)-D(z)
 &=\sum_i\bigl(B_i(\bar\sigma)-U_i(\bar\sigma)-b_i+u_i\bigr)\\
 &=\sum_Se(S)R(S)-\sum_i\Delta_i.
\end{aligned}
\]

If (z) is globally minimizing, (\bar\sigma) is an actual profile and its
semantic pair belongs to the carrier, so the left side is nonnegative.  This
proves (B).  If no actual profile achieves the minimum value, the left side is
strictly positive.  Under (C), however, the escaped reward moment is
nonpositive while the cap drop is nonnegative, so (A) makes the left side
nonpositive.  Global minimality forces equality, and (\bar\sigma) is an
actual minimum-value profile.

The note's phrase “every positive global minimum is attained” has already
been repaired to refer to the minimum **value**.  The proof is stronger still:
(D_*>0) is not used in the attainment argument.  Positivity is needed only
when this theorem is placed in the no-uniform-payoff branch.

## Exact boundary tests and falsification attempts

### Nonnegative singleton rewards are necessary for the cap inequality

Take two players (i,j).  Give player (i) reward (-1) at every nonempty
terminal coalition.  Let (i) play Never and let (j) quit deterministically
at date (n).  Against this profile, every pure time and Never gives player
(i) payoff (-1), so (B_i(\sigma_n)=-1).  The law of (j)'s clock converges
to Never.  Against the all-Never limiting opponent, player (i)'s Never reply
gives zero, hence (B_i(\bar\sigma)=0).  Thus

\[
 B_i(\bar\sigma)=0> -1=\liminf_nB_i(\sigma_n).
\]

This falsifies the cap semicontinuity conclusion when
(r_i(\{i\})=-1), exactly at the stated sign boundary.

### Global minimality is necessary

The note's two-player example is correct.  With players (c,a), rewards

\[
 r_c(S)=0,\qquad
 r_a(\{c\})=-1,quad r_a(\{a\})=0,quad r_a(\{c,a\})=1,
\]

and (c) uniform on (0,\ldots,n) while (a) Never, one has

\[
 U=(0,-1),\qquad B=(0,1/(n+1)).
\]

For (0\le t\le n), the value to (a) of quitting at (t) is
((1-t)/(n+1)); later times and Never give (-1).  Thus the cap is exactly
(1/(n+1)).  Both laws converge to Never and the semantic pairs converge to
(((0,-1),(0,0))), of debt one.  Any profile with (U_a=-1) must terminate
at (\{c\}) almost surely.  The proper finite stopping law of (c) has a
least positive-support date (t_0); quitting at (t_0) gives (a) the
strictly positive value (\Pr(T_c=t_0)).  The limit point is therefore not
realized.  All-Never has debt zero, so the positive-debt limit is not a global
minimum.

This example is stronger in singleton signs than the already formalized
positive-debt nonclosedness table: here both own singleton rewards are zero.
It still has global minimum zero and is not a counterexample to uniform
equilibrium.

### Social-reward sign is a sufficient chamber, not a necessary condition

Nothing in the proof says that a positive (R(S)) forces nonattainment.  It
only says that a genuinely unattained minimum value under nonnegative own
singletons must have strictly positive escaped aggregate reward after the cap
drop is paid.  An attained minimum may coexist with positive-social-reward
coalitions.  The implication must not be advertised as an equivalence.

## Freshness and overlap audit

The following checked declarations supply genuine inputs but do not contain
the social-surplus theorem:

- `CompactStoppingLaw` and its PMF reconstruction in
  `MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingTerminalPayoff_update_compactStoppingLawProfile_finiteTime_tendsto`
  and
  `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_singleton` in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
- `nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier` and
  `exists_terminalSemanticSelectedLawLimit_with_all_nonproper` in that same
  file; and
- `terminalSemanticLawCarrier_rewardMoment` and the joint-law carrier lift in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`.

`formalized/OPPONENT_TIGHT_TERMINAL_SEMANTIC_REALIZATION.md` realizes the full
semantic pair under opponent tightness and reduces a nonattained minimum with
nonnegative singleton rewards to one selected all-nonproper law limit.  It
does not prove coordinatewise nonnegativity of the escaped terminal-law
defect, cap lower semicontinuity in this non-tight arm, identity (A), the
strict social-surplus packet, or the sign-chamber attainment theorem.

`formalized/POSITIVE_DEBT_TERMINAL_SEMANTIC_NONATTAINMENT.md` proves a related
two-player nonclosedness example, but one own singleton reward is negative.
The note's two-player example is therefore a new sharper boundary test, not a
duplicate.  Narrow searches in `UniformEquilibrium/`, `Research/`,
`formalized/`, and `exports/` found no declaration or packet proving (A)--(C).

## Conjecture-facing adapter and consumer

The actual-data adapter should be stated explicitly in the export packet:

1. choose a global carrier minimizer (z);
2. use `nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier` to retain an
   actual realizing sequence and one common coordinatewise weak-law limit;
3. pass to a further subsequence in the finite outcome simplex; and
4. reconstruct (\bar\sigma) from the limiting laws.

Under (C), the theorem then gives an actual profile with debt exactly (D_*).
In the positive-minimum/no-uniform-payoff branch, this output can be fed to the
checked actual-profile paid-cap machinery.  In particular,
`QuittingActualProfileTerminalGapPaidCapPort.inertStall_of_minimumFiber` in
`ActualProfileTerminalGapPaidCap.lean`, or equivalently the exact-fibre
contraction declarations in `PaidCapMinimumFiberContraction.lean`, forces any
such paid cap port into its literal inert-stall arm.  This is a real transition
from the all-nonproper nonattainment seam to the existing actual-minimum inert
seam; it is not a uniform-equilibrium consumer.

Universally, without the aggregate sign condition, (B) strictly narrows the
all-nonproper nonattainment arm named by
`exists_terminalSemanticSelectedLawLimit_with_all_nonproper`: a genuinely
unattained minimum value must carry escaped positive social surplus exceeding
the complete downward cap jump.  No current theorem consumes that positive
surplus packet.

## Required repairs before export

1. State the theorem for a finite nonempty player set and define the complete
   outcome law, including Never.
2. Replace the phrase “assume the stopping laws converge to an actual
   profile” by weak convergence of the laws followed by explicit behavioral
   reconstruction.
3. Include the finite-horizon or Portmanteau proof of (e(S)\ge0), rather than
   citing an unnamed compact-outcome bubble argument.
4. Include the carrier-to-selected-law-limit and finite-outcome-subsequence
   adapter needed for the unconditional attainment corollary.
5. State the strongest conclusion: the global minimum value is achieved under
   (C), with no (D_*>0) assumption.  Keep the weaker positive version as the
   conjecture-facing corollary if desired.
6. Add the negative-singleton cap-jump counterexample above, and retain the
   note's global-minimality counterexample.
7. Name the actual-minimum inert-stall consumer and state explicitly that it
   does not prove a uniform-equilibrium payoff when (D_*>0).
8. Give Lean-facing theorem shapes for the escaped-mass inequality, cap
   lower-semicontinuity, debt account, and attained-minimum corollary.  Do not
   assume the defect law or reconstructed semantic pair as structure fields.

After these repairs, I recommend **PASS for export** as a complete reduction
of the checked all-nonproper minimum-attainment seam and a special sign-chamber
attainment theorem.  As written, the result should remain in `notes/` rather
than be copied verbatim to `exports/`.
