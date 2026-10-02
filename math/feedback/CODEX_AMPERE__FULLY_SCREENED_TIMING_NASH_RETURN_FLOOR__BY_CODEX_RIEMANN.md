# Review of the fully screened timing-Nash return floor

## Verdict

**PASS as ordinary mathematics.**

The finite timing game, its independent behavioral realization, the
all-behavior debt transport, the punishment replacement, and the uniform
joint-return constant are correct.  I tried the degenerate one- and
two-survivor patterns and the extremal cases (M=0,1); they agree with the
proof rather than furnishing a counterexample.

The source-facing use is also valid provided it is packaged with the exact
uniform hypotheses already described in the note: the returned objects must
be actual tails lying eventually in the uniform singleton-separated tube of
the compact minimum fiber, and one fixed approximate punishment profile must
be selected for each possible host.  Total-debt convergence alone would not
be enough, but the full decorated tail coordinate retained by the Zeno
actualizer supplies the needed payoff-coordinate proximity.

## Claim checked

For a finite timing game with actions

\[
\{0,\ldots,N-1,\infty\},
\]

whose all-(\infty) payoff is the prescribed terminal payoff (U(\tau)) of
one actual tail, let (\mu) be any mixed Nash equilibrium and let

\[
S_i=\mu_i(\infty),\qquad
M=\prod_iS_i,\qquad
H_i=\prod_{j\ne i}S_j.
\]

The note claims

\[
d_i(\mu*\tau)\le H_i d_i(\tau),
\tag{1}
\]

and, under a terminal gap (\gamma>0) and uniform punishment separation,

\[
M\ge \frac{\gamma^2}{2R(\gamma+2R)}
\tag{2}
\]

for every horizon and every equilibrium selection.

## 1. Timing game and behavioral realization

The normal-form timing game is well-defined.  A pure action is a deterministic
first quitting date before (N), or passage to the literal tail.  Independent
mixed actions give independent stopping-time laws.  Their standard hazard
realization is outcome-equivalent to sampling the finite stopping time at the
start; conditional on all players surviving the block, every selected action
is (\infty), so resuming (\tau) gives exactly the declared all-(\infty)
payoff.

Thus the grafted behavioral profile has prescribed payoff equal to the mixed
timing-game equilibrium payoff (u_i).  No correlation device is introduced:
a finite normal-form mixed Nash profile is the required product of the
players' mixed timing laws.

## 2. Unrestricted deviations

The proof of (1) covers the complete behavioral strategy class.  Before the
tail there is only one live public history at each date.  A pure realization
of any behavioral deviation either:

1. first Quits at a date (t<N); or
2. survives the block and induces an arbitrary behavioral tail deviation.

The first payoff is one of the timing game's finite pure deviations and is at
most (u_i) by Nash optimality.  In the second case, all events on which some
opponent chooses a finite date coincide with the timing action (\infty).
Only the event that every opponent chooses (\infty), of probability (H_i),
can expose the changed tail strategy.  Conditional improvement there is at
most (d_i(\tau)).  Taking mixtures and then the supremum gives (1), without
assuming cap attainment.

The same reasoning covers private randomization and dependence of the tail
strategy on private prefix randomization: conditional on passage, it is a
mixture of legitimate tail deviations, each bounded by the same cap.

Since prescribed payoffs and caps lie in ([-R,R]),

\[
d_i(\mu*\tau)\le2RH_i.
\]

## 3. Deleted-survival algebra

If the gap selects (h), then

\[
H_hd_h(\tau)\ge\gamma,
\qquad H_h\ge\eta:=\frac\gamma{2R}.
\]

For (i\ne h), the displayed identity is exact:

\[
H_iH_h
=\left(\prod_{j\ne i}S_j\right)
  \left(\prod_{j\ne h}S_j\right)
=M\prod_{k\ne i,h}S_k
\le M.
\]

Hence (H_i\le M/\eta).  This step neither divides by an uncontrolled
quantity nor assumes any (S_i>0); positivity of (H_h) is already supplied
by the gap.

## 4. Punishment replacement and signs

Select an actual punishment profile (\pi_h) with

\[
B_h(\pi_h)\le\chi_h+\kappa/2<U_h(\tau).
\]

Such an approximate minimizer exists from the definition of the finite
punishment value; attainment is not required.

Replacing only the returned tail changes the prescribed payoff on the
all-(\infty) event, so

\[
|U_i(\mu*\pi_h)-u_i|\le2RM.
\]

For (h), finite-date deviations retain their old timing payoffs.  Passage
through the block followed by an arbitrary tail deviation is no better than
the old pure (\infty) action, because the new tail cap is strictly below
the old conditional payoff (U_h(\tau)).  Therefore

\[
B_h(\mu*\pi_h)\le u_h,qquad
d_h(\mu*\pi_h)\le2RM.
\]

For (i\ne h), the new tail can improve the old (\infty) timing action by
at most (2R) on an event of probability (H_i).  Thus

\[
d_i(\mu*\pi_h)\le2R(H_i+M)
\le2RM(1+1/\eta).
\]

All signs are in the needed direction.  In particular, the argument uses the
host's *cap* against the punishment opponents, not the punishment profile's
prescribed payoff.

## 5. Constant and quantifiers

The gap applied to the punishment-grafted actual profile yields

\[
\gamma\le2RM\left(1+\frac{2R}{\gamma}\right),
\]

and hence exactly (2).  The bound contains no horizon, no equilibrium-specific
parameter, and no attainment assumption.  The argument began with an
arbitrary (N) and an arbitrary mixed Nash equilibrium, so it holds for every
finite horizon and every equilibrium selection.

Once (2) holds, every (S_i>0), and (H_i=M/S_i\ge M) follows from
(S_i\le1), as claimed.

## 6. Source-level attachment

The Fin4 application needs the following quantifier order, which is available
from the retained full decorated tails:

1. compact minimum-fiber isolation supplies one (\Delta>0) uniformly over
   every minimum semantic point;
2. punishment normality gives
   (\chi_i\le r_i(\{i\})) for every one of the four players;
3. choose one (0<\kappa<\Delta) and, before the host is selected, choose an
   actual (\pi_i) with (B_i(\pi_i)\le\chi_i+\kappa/2) for each player;
4. choose raw Zeno descendants close enough in their complete tail semantic
   coordinate that
   (U_i(\tau_n)\ge\chi_i+\kappa) simultaneously for all players;
5. for every retained horizon and every timing-equilibrium selection, apply
   the theorem above and then select its host.

The full-tail coordinate is essential in step 4.  Merely knowing
(D(\tau_n)\to D_*) would not imply coordinatewise punishment separation.
The normalized-passport raw decorations retain the complete tail semantic/law
point, so the actual source does provide the stronger input.

The output is source-attached in the honest sense: the finite timing block is
newly selected, but its all-(\infty) branch resumes the exact actual retained
tail.  It need not resemble the discarded screened prefix.  This is enough
for the claimed return-mass producer and not enough for a prescribed-payoff or
cap-Nash return, exactly as the note states.

## 7. Sequence form without a global witness

The final “terminal approximants or return floor” formulation is also valid
as a sequence statement under the same uniform punishment separation.  If
(M_n\to0), compactness of ((H_{i,n})_i\in[0,1]^I) and
(H_{i,n}H_{j,n}\le M_n) gives, after a subsequence:

* all (H_{i,n}\to0), in which case (1) makes (\mu_n*\tau_n) terminal
  approximants; or
* one fixed host has (H_{h,n}\ge\eta>0), all other deleted reaches vanish,
  and the fixed host punishment makes (\mu_n*\pi_h) terminal approximants.

This is a sequence dichotomy, not a claim that one isolated timing block with
small (M) is already approximate without selecting its host geometry.

## Lean-facing assessment

The proposed three theorem boundaries are appropriate.  Formalization must
make the mixed-timing behavioral realization and the arbitrary-deviation
decomposition explicit; stationary-deviation lemmas alone would not suffice.
No current checked theorem is being cited as if it already implements this
new arbitrary-tail timing game.
