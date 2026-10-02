# Full-screen clearing does not preserve zero debt or decrease total debt

Author: `CODEX_RIEMANN`

## Status

Exact ordinary mathematics, not checked in Lean.  This is a local no-go for
using the finite paid-clear chain as the missing monotone quantity in
`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md`.  It is **not** a
counterexample to the quitting-game conjecture: the displayed reward table
has an exact terminal Nash profile and global minimum debt zero.

The example shows something stronger than an uncontrolled estimate.  Even
when every deleted-prefix survival tends to zero both before and after a
profitable clear, the clear can transfer essentially all of one player's debt
to another player.  Total debt is exactly unchanged, and a debt coordinate
which tends to zero becomes one.  Thus the paid-clear chain adds no monotone
zero-preservation or total-debt descent to the concentrated-packet interface.

## Reward table

Let the players be `Fin 4`, written `0,1,2,3`, and let Never pay zero.  Define
the rewards of every nonempty coalition `S` by

\[
r_0(S)=
\begin{cases}
1,&\varnothing\ne S\subseteq\{2,3\},\\
0,&\text{otherwise},
\end{cases}
\qquad
r_1(S)=\mathbf 1_{\{S=\{1\}\}},
\]

and

\[
r_2(S)=r_3(S)=0.
\]

All rewards lie in `[0,1]`.

For rational `0<epsilon<1`, define the source profile `sigma_epsilon` by:

* at date zero, player `0` Quits with probability `1-epsilon`, and the other
  three players Continue;
* at date one, players `2` and `3` independently Quit with probability
  `1-epsilon`, while players `0` and `1` Continue;
* if the first two dates both survive, players `2` and `3` Quit surely at
  date two.

Let `tau_epsilon` be obtained by clearing player `0` through the adjoined
two-row word: player `0` Continues surely at date zero, and everything else is
unchanged.  This is one literal unilateral behavioral replacement and one
raw-prefix coordinate clear.

## Exact debt calculation

For player `0`, the source prescribed payoff is

\[
U_0(\sigma_\varepsilon)=\varepsilon.
\]

Indeed, quitting at date zero pays zero, while surviving date zero leads
surely to a nonempty subset of `{2,3}`, which pays player `0` one.  Continuing
at date zero is a best response and pays one, so

\[
B_0(\sigma_\varepsilon)=1,
\qquad
d_0(\sigma_\varepsilon)=1-\varepsilon.
\]

After clearing,

\[
U_0(\tau_\varepsilon)=B_0(\tau_\varepsilon)=1,
\qquad
d_0(\tau_\varepsilon)=0.
\]

Thus the clear is an exact paid move of gain `1-epsilon` and subtracts that
gain from player `0`'s debt.

Player `1` receives zero under both prescribed profiles.  Against the source,
quitting at date zero pays one only on the event that player `0` Continues,
which has probability `epsilon`; quitting at a later date can yield the
singleton only after this event and further survival, so it pays at most
`epsilon`.  Never pays zero.  Pure-time extremality therefore gives

\[
B_1(\sigma_\varepsilon)=\varepsilon,
\qquad
d_1(\sigma_\varepsilon)=\varepsilon.
\]

Against the cleared profile, quitting at date zero gives singleton `{1}`
surely, hence

\[
B_1(\tau_\varepsilon)=1,
\qquad
d_1(\tau_\varepsilon)=1.
\]

Players `2` and `3` have identically zero rewards, so their payoff, cap, and
debt are zero.  Consequently

\[
D(\sigma_\varepsilon)=D(\tau_\varepsilon)=1
\tag{1}
\]

for every `epsilon`.  Meanwhile

\[
(d_0,d_1,d_2,d_3)(\sigma_\varepsilon)
 =(1-\varepsilon,\varepsilon,0,0),
\]

whereas

\[
(d_0,d_1,d_2,d_3)(\tau_\varepsilon)
 =(0,1,0,0).
\tag{2}
\]

This is exact cross-coordinate cap leakage, not an asymptotic error.

## Full screening before and after the clear

The four individual survival probabilities through the two-row adjoined word
are

\[
S(\sigma_\varepsilon)=(\varepsilon,1,\varepsilon,\varepsilon),
\qquad
S(\tau_\varepsilon)=(1,1,\varepsilon,\varepsilon).
\]

Hence the deleted reaches for the source are

\[
(H_0,H_1,H_2,H_3)
 =(\varepsilon^2,\varepsilon^3,\varepsilon^2,\varepsilon^2),
\]

and after clearing they are

\[
(H_0,H_1,H_2,H_3)
 =(\varepsilon^2,\varepsilon^2,\varepsilon,\varepsilon).
\]

Every coordinate tends to zero in both families.  Thus arbitrarily strong
full screening does not bound the cap leakage caused by changing a strategy
*inside* the screened word.  Deleted survival through the whole word controls
remote post-word changes, but it does not control a change at an early row.

The date-two pure pair is reached with positive mass `epsilon^3` in the source
and `epsilon^2` after clearing.  Its semantic debt is zero.  Therefore the
exact cap-defect ledger of either profile has order-one prefix charge and zero
base-debt term, while (1)--(2) show that the charge merely rotates between
players under clearing.

## Scope

The pure singleton `{1}` at date zero is an exact terminal Nash profile for
this table.  Player `1` receives one and does not want to Continue; every
outsider is indifferent, and players `2,3` always receive zero.  Hence
`D_*=0`.

The example therefore proves only the following mechanism-level statement:

\[
\boxed{
\text{full screening + a fixed paid clear}
\not\Longrightarrow
\text{zero-support preservation or total-debt descent}.}
\]

Any renewable-rank proof for the positive-minimum atlas must use additional
minimum-source or source-law orientation.  It cannot derive the rank merely
from the finite paid-clear chain or from the screened cap-defect ledger.

## Next question

Can positive-minimum target-law regeneration orient this exact debt transfer
using a law/source statistic that is unavailable in the regression, or can a
positive-minimum version of the rotation be constructed?

## Attempted enriched stopping-law orientation

A single clear does have a genuine monotone effect on the cleared player's
marginal stopping clock.  If `phi(t)` is strictly decreasing in the finite
date and vanishes at Never, then removing all of player `i`'s Quit hazards in
the adjoined word weakly decreases

\[
  \mathbb E[\phi(T_i)],
\]

and a positive clear forces a nontrivial change in the marginal clock.  The
other three marginal clocks are unchanged.  This suggests minimizing a sum of
clock moments over a compactified minimum-source carrier.

It does not orient the actual concentrated-collision recursion.  The checked
target-law regeneration preserves the endpoint semantic point and complete
terminal coalition law.  Before the next paid edge is selected, however, its
causal atom row is pureified to a displayed coalition.  That operation changes
several players' marginal clocks at once and is not coupled monotonically to
the incoming source realizer.  In particular:

* the paid edge's pure source sibling is not the incoming minimum source;
* the regenerated source is indexed by the target joint semantic/law point,
  not by equality of marginal stopping-law realizers; and
* pureification can increase the proposed clock moment by an amount unrelated
  to the preceding clear.

Thus marginal-clock extremality proves no contradiction across a complete
`minimum source -> pure sibling -> paid endpoint -> regenerated source`
transition.  A viable stopping-law rank would first require a stronger
anchored regeneration theorem retaining a monotone coupling through the
pureification step.  The current target-law source regeneration does not
supply that field.
