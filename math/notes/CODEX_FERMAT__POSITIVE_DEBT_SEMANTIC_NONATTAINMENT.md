# Positive debt does not make terminal semantics attainable

Author: `CODEX_FERMAT` (counterexample supplied by the user; source audit and
packaging by the conference coordinator)

Status: **complete ordinary-mathematics counterexample; two independent
falsification reviews requested.**  The example refutes closedness of the
attained terminal-semantic set on a positive-debt slice.  It does not refute
attainment on a globally positive minimum-debt fiber.

## 1. Exact question and answer

For a finite quitting reward table `r`, let

\[
 \mathcal S_r=\{\operatorname{Sem}(\sigma):\sigma
   \text{ is an actual behavioral profile}\}
\]

and let `K_r` be its closure, the terminal-semantic carrier.  Write

\[
 D(U,B)=\sum_i(B_i-U_i).
\]

The proposed assertion was that

\[
 \mathcal S_r\cap\{D\ge\delta\}
\]

is closed for every `delta>0`, equivalently that a carrier point of positive
debt which is the limit of actual semantic pairs is itself realized by an
actual behavioral profile.

This is false already for two players, and two players are minimal.

## 2. Two-player table and diffuse profiles

Let the players be `c` (clock) and `a` (atom tester), and order payoff
coordinates as `(c,a)`.  Define

\[
 r(\{c\})=(-1,0),\qquad
 r(\{a\})=(0,0),\qquad
 r(\{c,a\})=(0,1).                                  \tag{2.1}
\]

Infinite all-Continue play pays zero.  For `n>=1`, let player `a` play Never
and let player `c` use the hazards

\[
 q_c^{(n)}(t)=
 \begin{cases}
 1/(n-t),&0\le t<n,\\
 0,&t\ge n.
 \end{cases}                                        \tag{2.2}
\]

The last relevant hazard is one.  Telescoping gives

\[
 \Pr(T_c\ge t)=\frac{n-t}{n},\qquad
 \Pr(T_c=t)=\frac1n\quad(0\le t<n).                 \tag{2.3}
\]

Thus `T_c` is uniform on `{0,...,n-1}`.

Prescribed play always stops at `{c}`, so

\[
 U(\sigma_n)=(-1,0).                                \tag{2.4}
\]

Against `a`'s Never strategy, every finite quit by `c` pays `-1` and Never
pays zero.  Therefore

\[
 B_c(\sigma_n)=0.                                   \tag{2.5}
\]

If `a` quits at deterministic time `t`, it gets one exactly on the event
`T_c=t`.  Exact pure-time extremality consequently gives

\[
 B_a(\sigma_n)=\sup_t\Pr(T_c=t)=\frac1n.            \tag{2.6}
\]

Hence

\[
 z_n=\operatorname{Sem}(\sigma_n)
   =\left((-1,0),(0,1/n)\right)
   \longrightarrow z=\left((-1,0),(0,0)\right),     \tag{2.7}
\]

while

\[
 D(z_n)=1+1/n,\qquad D(z)=1.                        \tag{2.8}
\]

In particular `z in K_r` and every `z_n` lies in the slice `D>=1`.

## 3. The limit point is not attained

Suppose an arbitrary behavioral profile `sigma` realized `z`.  Since player
`c` gets `-1` exactly when the terminal coalition is `{c}` and zero on every
other terminal outcome and on nonabsorption,

\[
 U_c(\sigma)=-\Pr_\sigma(\text{terminal coalition is }\{c\}). \tag{3.1}
\]

The required equality `U_c=-1` forces `{c}` to occur almost surely.  In
particular player `c` has a finite complete stopping time almost surely.  Its
law is a probability measure on the countable set `Nat`, so there is a date
`t` with

\[
 \Pr(T_c=t)>0.                                      \tag{3.2}
\]

If player `a` deviates to deterministic quit time `t`, it earns one exactly
on this event and zero otherwise.  Thus

\[
 U_a(\sigma[a\leftarrow Q_t^a])=\Pr(T_c=t)>0,       \tag{3.3}
\]

so `B_a(sigma)>0`, contradicting the required cap coordinate `B_a=0`.
This argument places no stationarity, support, memory, or finite-horizon
restriction on `sigma`.

Therefore

\[
 z\notin\mathcal S_r,
 \qquad
 \mathcal S_r\cap\{D\ge1\}\text{ is not closed}.   \tag{3.4}
\]

## 4. Exact missing face endpoint

On the face `U_c=-1`, actual play must terminate at `{c}` almost surely.  If

\[
 \mu(t)=\Pr(T_c=t),
\]

then exact pure-time extremality gives

\[
 B_a=\sup_t\mu(t)>0.                                \tag{4.1}
\]

Conversely, every `alpha in (0,1]` is the largest atom of some probability
distribution on `Nat`: choose a sufficiently large finite support and split
the remaining mass into atoms no larger than `alpha`.  Taking `a` to play
Never realizes the corresponding semantic point.  Hence

\[
 \mathcal S_r\cap\{U_c=-1\}
 =\left\{\left((-1,0),(0,\alpha)\right):0<\alpha\le1\right\}, \tag{4.2}
\]

whose closure adds exactly the unrealized endpoint `alpha=0`.

## 5. Global-minimum caveat

The all-Never profile has `U=B=(0,0)`, so this table has global minimum debt

\[
 D_*=0.                                             \tag{5.1}
\]

The point `z` is only a minimum on the carrier face `U_c=-1`: there `c` has
cap zero and debt one, so `D>=1`.  Consequently the example refutes
realizability from `D(z)>0` alone, but not the stronger statement

\[
 D(z)=D_*>0.                                        \tag{5.2}
\]

That positive-global-minimum version remains the conjecture-facing compactness
question.

## 6. Minimality of two players

For one player with singleton reward `rho`, a behavioral profile is
semantically determined by its eventual quitting probability `p in [0,1]`:

\[
 U=p\rho,\qquad B=\max\{\rho,0\}.                   \tag{6.1}
\]

The attained semantic set is therefore a closed line segment.  Thus the
two-player example is cardinal-minimal.

## 7. Probability and strategy audit

The profiles use only private behavioral hazards along the unique live
history.  Formula (2.3) is the exact induced complete stopping law.  The cap
calculation for `a` covers every behavioral deviation through the checked
fact that a fixed-opponent quitting payoff is a mixture of deterministic
quit-time and Never values; its supremum is the largest atom of `T_c`.

In the nonattainment proof, the prescribed strategy of `a` is unrestricted.
The conclusion uses only the actual terminal outcome identity (3.1) and one
legal deterministic deviation.  No coupling between players' private
randomizers is assumed beyond the game's product behavioral semantics.

## 8. Source correspondence

The relevant checked pure-time theorem is
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/`
`TerminalSemanticPositiveSlopeRectangle.lean`.

The nearby fixed-table diffuse regressions
`TerminalSemanticFixedTableDiffuseIncidenceRegression.lean` and
`TerminalSemanticFixedTableCapDefectRegression.lean` concern persistent
incidence versus vanishing local root defect on a three-player table.  They do
not state nonclosedness of the attained semantic set or the exact two-player
face (4.2).

The reviewed
`CODEX_MINER__ACTUAL_PAID_FIRST_DISAGREEMENT_SUFFIX_COMPACTIFICATION.md`
contains a different two-player regression: after normalizing a paid row, the
observer's own survival can vanish despite unit deleted survival.  It does not
identify a positive-debt carrier point which is not attained.  The examples
share the diffuse-clock mechanism but refute different implications.

## 9. Conjecture-facing change and nonclaims

This result removes the broad compactness shortcut

\[
 z_n\in\mathcal S_r,\ z_n\to z,\ D(z)>0
 \Longrightarrow z\in\mathcal S_r.
\]

It shows that positive debt alone does not prevent temporal mass from
escaping to infinity.  It does not exclude a theorem using the global
positive-minimum hypothesis, punishment normality, a terminal gap, or a
literal source chronology.  It neither proves nor disproves the uniform-
equilibrium conjecture.

## 10. Lean handoff

Use a two-element player type.  Define the reward table (2.1), the uniform
finite stopping law through hazards (2.2), and prove the semantic coordinates
(2.4)--(2.6).  The carrier membership of `z` follows from the convergent
actual sequence.  Nonattainment should be stated by quantifying over an
arbitrary behavioral profile and extracting a positive atom from the
countably supported almost-sure finite stopping law of `c`; do not restrict
the candidate profile to a stationary or explicit-law subclass.

The one-player minimality statement can be formalized separately and is not
needed for the core nonclosedness theorem.
