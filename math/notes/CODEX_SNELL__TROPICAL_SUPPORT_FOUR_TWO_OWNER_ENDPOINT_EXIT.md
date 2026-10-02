# A two-owner endpoint exit completes the tropical support-four descent

Author: `CODEX_SNELL`

## Status

**Complete proof draft, ordinary mathematics, not checked in Lean.**  This
note starts at the actual two-owner child produced by the reviewed tropical
two-Never chronological descent from full support.  It proves that a third
literal exact-cap endpoint update either is already a Quit-now off-minimum
paid exit or is a Never deletion to a genuine diffuse singleton descendant.
In the latter case the reviewed origin-independent negative-column collar
theorem applies to this exact singleton child and supplies a fourth literal
exact-cap Quit-now off-minimum paid exit.

The result is finite-profile and chronological.  It neither lifts a
two-player equilibrium nor identifies response siblings.

## Question

Let a positive-clearance full-support stationary Fin4 source be followed by
the two exact Never updates in
[`CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md`](CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md).
The actual child has two remaining stationary owners.  Must this child admit
another literal cap response leading to a singleton or to the known
off-minimum paid-port waist?

Yes.  The sign of the two cross entries gives the first split.  If both
entries vanish, homogeneous infeasibility forces a removed player to prefer
Quit now strictly to its prescribed Never strategy.

## 1. Exact two-owner setting

Let \(I=\operatorname{Fin}4\), let

\[
 s_a=r_a(\{a\}),\qquad A_{a\ell}=r_a(\{\ell\})-s_a,
\]

and suppose

\[
 \neg\operatorname{HasHomogeneousSimplexSolution}(A).             \tag{1.1}
\]

Let \(\lambda\in(0,1)^I\) have total mass one.  Start with stationary
hazards \(x_{n,a}>0\) such that

\[
 h_n=\sum_a x_{n,a}\to0,
 \qquad x_{n,a}/h_n\to\lambda_a.                                  \tag{1.2}
\]

Suppose two fixed players have already been changed, successively and
literally, to Never.  Denote the remaining pair by

\[
 B=\{p,k\},\qquad \Lambda=\lambda_p+\lambda_k>0,                  \tag{1.3}
\]

and denote the actual child by \(\tau_n\).  Thus \(p,k\) retain their exact
source stationary hazards, while both players outside \(B\) are literal
Never.  This is exactly the support-two child produced from initial support
four; there are no hidden lower-order active outsiders.

Its terminal law converges in total variation to

\[
 \nu_B=\frac{\lambda_p}{\Lambda}\delta_{\{p\}}
       +\frac{\lambda_k}{\Lambda}\delta_{\{k\}}.                 \tag{1.4}
\]

For any player \(a\), write \(Q_{n,a}\) for the payoff from Quit at date zero
against \(\tau_{n,-a}\), and \(N_{n,a}\) for the payoff from literal Never.
Because every opponent is stationary, every deterministic pure quit time
has payoff between these two endpoints, both endpoints are attained, and
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` makes

\[
 B_a(\tau_n)=\max\{Q_{n,a},N_{n,a}\}                              \tag{1.5}
\]

the exact cap over every unilateral behavioral deviation.

## 2. Active-owner endpoint signs

For the active owner \(p\),

\[
 Q_{n,p}\to s_p,\qquad N_{n,p}\to s_p+A_{pk},                    \tag{2.1}
\]

and

\[
 U_p(\tau_n)\to
 s_p+\frac{\lambda_k}{\Lambda}A_{pk}.                             \tag{2.2}
\]

Consequently:

- if \(A_{pk}>0\), literal Never is the exact unrestricted cap for every
  sufficiently large \(n\), its actual gain tends to

  \[
   \frac{\lambda_p}{\Lambda}A_{pk}>0,                             \tag{2.3}
  \]

  and the literal child is a stationary one-leading-owner source owned by
  \(k\);
- if \(A_{pk}<0\), Quit at date zero is the exact unrestricted cap for every
  sufficiently large \(n\), and its actual gain tends to

  \[
   -\frac{\lambda_k}{\Lambda}A_{pk}>0.                            \tag{2.4}
  \]

The identical statements hold after interchanging \(p\) and \(k\).

### Proof

Against a Never deviation by \(p\), player \(k\)'s positive stationary
hazard eventually absorbs alone, giving the second limit in (2.1) exactly
up to no error at all from other owners.  Quit at date zero collides with
\(k\) with probability \(x_{n,k}\to0\), giving the first limit.  Formula
(1.4) gives (2.2).  A strict sign separates the endpoint limits.  Equation
(1.5) then proves exact finite-\(n\) cap attainment, and subtracting (2.2)
from the appropriate endpoint gives (2.3) or (2.4).

## 3. The zero-cross case forces an outsider Quit response

Assume now

\[
 A_{pk}=A_{kp}=0.                                                  \tag{3.1}
\]

Define the probability vector supported on \(B\) by

\[
 \mu_p=\lambda_p/\Lambda,\qquad
 \mu_k=\lambda_k/\Lambda,\qquad
 \mu_a=0\quad(a\notin B).                                        \tag{3.2}
\]

For the two support owners, (3.1) and the zero diagonal give

\[
 (A\mu)_p=(A\mu)_k=0.                                             \tag{3.3}
\]

If every outsider \(a\notin B\) satisfied \((A\mu)_a\ge0\), then
\(\mu\) would be a homogeneous simplex solution: it is nonnegative, has
total mass one, \(A\mu\ge0\), and
\(\mu_a(A\mu)_a=0\) for every player.  This contradicts (1.1).  Hence one
fixed outsider \(b\notin B\) satisfies

\[
 R_b:=(A\mu)_b
 =\frac{\lambda_pA_{bp}+\lambda_kA_{bk}}{\Lambda}<0.              \tag{3.4}
\]

At \(\tau_n\), this outsider is literally Never.  Therefore

\[
 U_b(\tau_n)=N_{n,b}\to s_b+R_b,
 \qquad Q_{n,b}\to s_b.                                          \tag{3.5}
\]

For all sufficiently large \(n\), Quit at date zero is its exact complete
behavioral cap, and the actual gain tends to

\[
 -R_b>0.                                                          \tag{3.6}
\]

This is a third literal source-attached update from the two-owner child.
Nonsingleton rewards do not affect (3.5): simultaneous Quit probability in
the date-zero row and collision probability in the stationary opponent law
both vanish with \(h_n\).

## 4. Positive-minimum collar and exhaustive dispatch

Assume now that the Fin4 game has no uniform-equilibrium payoff.  The checked
counterexample-side classification gives (1.1), and the compact terminal
semantic carrier has positive minimum total debt

\[
 D_*>0.                                                           \tag{4.1}
\]

For any cluster point \(y\) of terminal semantic pairs at which the selected
Quit-now endpoint is the exact limiting cap, one has

\[
 B_b(y)=s_b.                                                       \tag{4.2}
\]

For every minimum-fibre point \(z\),
`minimumTerminalSemantic_singletonMargin` gives

\[
 D_*\le B_b(z)-s_b=B_b(z)-B_b(y).                                 \tag{4.3}
\]

Thus \(y\) is strictly off the minimum fibre; compactness and continuity of
total semantic debt give \(D(\tau_n)\ge D_*+\delta\) eventually for some
\(\delta>0\).  The literal Quit-now update is a source-attached paid response
at this off-minimum collar.

Combining Sections 2 and 3 gives the exhaustive two-owner alternative:

1. if either cross entry is negative, an active owner has the exact-cap
   Quit-now off-minimum exit;
2. if both cross entries vanish, a removed outsider has the exact-cap
   Quit-now off-minimum exit; and
3. otherwise at least one cross entry is positive, the corresponding active
   owner has an exact-cap Never update to a genuine diffuse singleton source.

In case 3, apply the independently reviewed theorem
[`CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR.md`](CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR.md)
in its origin-independent frozen form, SHA-256
`89fb408340a6f20b9650a7a9bc34a19303287ff0cec7be9f881dacacc3154800`,
to that actual singleton child.  Its fixed negative-column blocker then has
an eventual exact-cap Quit-now response, and the child satisfies the same
positive-minimum collar.  Thus every branch reaches the source-attached
off-minimum paid-port/source-reentry waist after at most two further literal
updates.

### Literal paid-row audit

Every final response above is Quit at date zero from a stationary source
profile.  If its mover is active, its prescribed date-zero Continue
probability tends to one; if it is one of the removed outsiders, that
probability is exactly one.  The opponents' joint date-zero Continue
probability also tends to one.  Hence, on one common tail, the source mover's
Continue probability, opponent Continue probability, and joint source
Continue probability are each at least (1/2), while the row itself is
reached with probability one.  The strict limiting response gain has a fixed
positive half-limit lower bound.  The source continuation after its Continue
outcome is literally the same stationary source profile.  Thus this is a
profitable, source-attached first-disagreement row with complete cap and
chronological ancestry, not only a terminal-law comparison.

## 5. Conjecture-facing consequence

Together with the reviewed support descent, every support-cardinality output
of the period-one tropical source has a literal chronological dispatch:

- initial support two: one exact-cap Never deletion reaches a diffuse
  singleton, then the blocker gives an exact-cap Quit-now collar exit;
- initial support three: two exact-cap Never deletions reach a diffuse
  singleton, then the blocker gives the exit; and
- initial support four: two exact-cap Never deletions reach the two-owner
  child; Sections 2--4 give either an immediate Quit-now collar exit or a
  third Never deletion followed by the blocker exit.

This removes support reactivation as a separate tropical residual.  The
remaining obligation is exactly the existing quantitative off-minimum
paid-port/source-reentry waist: no theorem here turns the paid response into
a returned Nash--Bellman packet or terminal approximate Nash profiles.

## Source correspondence

The exact source and the first two chronological updates are the reviewed
exports/notes:

- `exports/FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md`;
- `notes/CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md`.

The singleton blocker/collar is
`notes/CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR.md`.
The named Lean declarations used here are:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`;
- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`;
- `singletonLCPFeasible_reindexMatrix_iff` and
  `exists_negative_entry_in_column_of_noHomogeneous`;
- `quittingTerminalSemanticCarrier_isCompact`;
- `continuous_quittingTerminalSemanticDebtSum`; and
- `minimumTerminalSemantic_singletonMargin`.

No inspected declaration already contains the two-owner sign dispatch or the
zero-cross homogeneous-infeasibility argument.

## Scope and nonclaims

- All cap claims are exact at each sufficiently large finite \(n\); only the
  displayed gains are limiting formulas.
- The two-owner child is the literal child of the first two Never updates.
  No separately selected profile is introduced.
- The zero-cross outsider is one of the two already removed players and is
  still literal Never before its displayed Quit-now update.
- The theorem controls complete behavioral caps, not only stationary or
  bounded-clock deviations.
- A Quit-now target is not treated as a regenerated diffuse singleton source;
  its deleted-player law retains the old owners.
- The result reaches but does not consume the quantitative off-minimum paid
  port.  No uniform equilibrium or renewable rank is claimed.

## Requested review

Please try to falsify the active-owner gain formulas (2.3)--(2.4), the
zero-cross use of homogeneous infeasibility, exact finite-\(n\) cap attainment
for the removed outsider, and the positive-minimum collar handoff.
