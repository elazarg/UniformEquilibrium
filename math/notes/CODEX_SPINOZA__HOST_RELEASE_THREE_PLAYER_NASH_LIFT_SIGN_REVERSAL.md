# A paid singleton-host release need not survive any three-player Nash lift

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; sharp adapter no-go, not Lean-checked.**  A
source-attached paid release of a unique early host into a deterministic
three-player late bubble does not by itself permit replacing that bubble by a
three-player Nash or uniform-equilibrium profile.  The four-player table below
has a release gain equal to one at the supplied late source, while every exact
terminal Nash profile of the deleted three-player game makes the same release
weakly worse than the old early host action.

The table has global minimum debt zero.  It is not a hard-residual
counterexample.  It proves that a positive theorem must use a global
positive-minimum/source constraint linking the chosen three-player continuation
to the supplied bubble; the three-player uniform-payoff theorem and the paid
source edge alone are insufficient.

## 1. Reward table

Use players \(0,1,2,3\), with player \(0\) the host.  Fix
\(\varepsilon\in(0,1)\).

For the three deleted-game players define, at every nonempty coalition \(S\),

\[
 r_1(S)=\varepsilon\,\mathbf 1_{\{1\in S\}},
\qquad
 r_2(S)=-\varepsilon\,\mathbf 1_{\{2\in S\}},
\qquad
 r_3(S)=-\varepsilon\,\mathbf 1_{\{3\in S\}}.
\tag{1.1}
\]

For the host, set

\[
 r_0(\{0\})=0,\qquad
 r_0(\{0,1\})=0,\qquad
 r_0(\{1\})=-1,\qquad
 r_0(I)=1,
\tag{1.2}
\]

and set every other host coordinate to zero.  The all-Never payoff is zero.

## 2. The supplied singleton-host source has a paid release

Let \(A\) be the pure-deadline profile

\[
 T_0=0,\qquad T_1=T_2=T_3=1.
\tag{2.1}
\]

Prescribed play stops at the singleton \(\{0\}\), so \(U_0(A)=0\).
If player \(0\) replaces its clock by \(T'_0=1\), all four players tie and
its payoff is \(r_0(I)=1\).  Against the three opponents at date one, every
host pure time has one of the values

\[
 r_0(\{0\})=0,\qquad r_0(I)=1,\qquad
 r_0(\{1,2,3\})=0.
\tag{2.2}
\]

Thus \(T'_0=1\) is an exact unrestricted cap response and

\[
 U_0(A[0\leftarrow T'_0])-U_0(A)=d_0(A)=1.
\tag{2.3}
\]

At the same source, player \(1\)'s only positive improvement is to join the
host at date zero, giving debt \(\varepsilon\), while players \(2,3\) have
debt zero.  Hence, for the scale \(\Gamma=1\),

\[
 d_i(A)<\Gamma\quad(i=1,2,3),
\qquad d_0(A)=\Gamma.
\tag{2.4}
\]

This is exactly the singleton-host release arm: all nonhosts lie below the
displayed release scale, and the host crosses the full gap into the late
three-player block.

## 3. Every deleted-game terminal Nash reverses the release comparison

Delete player \(0\) and consider the ordinary three-player quitting game on
\(J=\{1,2,3\}\) with rewards (1.1).  Let \(\rho\) be any exact terminal Nash
profile, with unrestricted behavioral deviations.

Player \(1\) can Quit at date zero and obtain \(\varepsilon\) surely,
regardless of the other two actions.  Its rewards never exceed
\(\varepsilon\), so its cap is exactly \(\varepsilon\).  Nash optimality
therefore gives

\[
 \Pr_\rho(1\text{ belongs to the finite terminal coalition})=1.
\tag{3.1}
\]

For \(i=2,3\), the prescribed payoff is
\(-\varepsilon\) times the probability that \(i\) belongs to the terminal
coalition.  By deviating to Never, player \(i\) obtains zero.  Nash
optimality forces

\[
 \Pr_\rho(i\text{ belongs to the finite terminal coalition})=0
 \qquad(i=2,3).
\tag{3.2}
\]

Consequently the deleted-game terminal coalition is \(\{1\}\) almost surely,
at some arbitrary finite random date \(\tau\).

Now restore player \(0\), first with the old early action \(e=0\).  If
\(\tau=0\), the terminal coalition is \(\{0,1\}\); if \(\tau>0\), it is
\(\{0\}\).  Both host rewards are zero, so

\[
 U_0(e,\rho)=0.
\tag{3.3}
\]

With the released action \(q=1\), the terminal coalition is \(\{1\}\) if
\(\tau=0\), \(\{0,1\}\) if \(\tau=1\), and \(\{0\}\) if
\(\tau>1\).  Therefore

\[
 U_0(q,\rho)=-\Pr_\rho(\tau=0)\le0=U_0(e,\rho).
\tag{3.4}
\]

Thus no exact deleted-game terminal Nash profile preserves even a positive
sign for the source comparison (2.3).

## 4. The regression is stronger than an arbitrary-selection failure

The obstruction does not come from choosing the wrong member of a large
three-player equilibrium set.  Equations (3.1)--(3.2) hold at every exact
terminal Nash profile of the deleted game and force its terminal coalition
law to be \(\delta_{\{1\}}\).  The calendar law of \(\tau\) may vary, but
(3.4) holds for every such law.

The source gain uses the simultaneous late coalition \(\{1,2,3\}\): joining
it creates the grand-coalition reward in (1.2).  Deleted-game Nash
optimality removes players \(2,3\) from the terminal coalition, because each
has a strict Never improvement whenever it participates.  The host's
release value then collapses.  This is an exact coalition-law displacement,
not a moving-deadline or cap-attainment issue.

## 5. Boundary and implication

The full four-player table has terminal equilibria and global minimum debt
zero; for example, players \(0,1\) may both Quit at date zero while players
\(2,3\) play Never.  The terminal coalition is \(\{0,1\}\).  Player \(0\)
would obtain \(-1\) by Continuing and player \(1\) would fall from
\(\varepsilon\) to zero; players \(2,3\) can only lower their zero payoff by
joining.  Hence no unilateral behavioral deviation gains.  The example does
not satisfy the positive-global-minimum hard residual.

What it rules out is the implication

\[
 \begin{array}{c}
 \text{source-attached paid host release into a three-player bubble}\\
 {}+\text{ existence of a three-player terminal Nash/UE}
 \end{array}
 \Longrightarrow
 \text{a host-cap-preserving four-player lift}.
\tag{5.1}
\]

A valid lift must additionally control the late coalition law seen by the
host, or use the positive minimum to charge its displacement.  Merely keeping
the host label, its two pure actions, and the source gain does not suffice.

## Sources inspected

- notes/CODEX_SPINOZA__FOUR_DEADLINE_SEMANTIC_COMPRESSION_AND_SINGLE_HOST_BUBBLE.md;
- formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md;
- notes/CODEX_AMPERE__FINITE_FIXATION_SPECTATOR_COMPRESSION_AND_HOST_ROTATION.md;
- questions/CARDINAL_MINIMAL_OUTSIDER_CONSUMER.md; and
- UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean.

## Next exact question

Can the positive global minimum price the change from the supplied late
coalition law to a three-player equilibrium law, yielding a paid return before
the host comparison changes sign?  Without such a law-linked charge, the
host-release/cardinal route ends at the same horizontal paid-port waist.
