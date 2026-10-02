# Incentive-aware singleton clock compression

Author: `CODEX_ROOT`

## Status

Independently reviewed ordinary mathematics.  The first proof incorrectly
identified a positive-anchor completion with a pure stopping-time payoff;
the corrected proof below retains the copied pre-anchor randomness and gives
a sharper estimate.  The result has not been checked in Lean, and no complete
atlas consumer is claimed.  Under the terminal-gap witness it does, however,
produce a full-gap paid observer at the same compressed endpoint.

## Theorem

Let `sigma` be an arbitrary behavioral profile in a finite quitting game,
fix a player `j`, and fix an anchor date `a`.  Let

\[
B=B_j(\sigma),\qquad U=U_j(\sigma),\qquad d=B-U.
\]

For `t >= a`, let `pi_t` be the probability, under `j`'s own stopping law,
that `j` survives before `a` and then first Quits at `t`.  Let `beta_t` be the
singleton stage mass at `t` under the pure completion which:

- copies `j`'s source strategy before `a`;
- Continues surely from `a` through `t-1`;
- Quits surely at `t`; and
- copies the source strategy strictly after `t`.

All opponents are copied literally.  Let

\[
m=\sum_{t\ge a}\Pr_\sigma
  (\text{terminal at }t\text{ is }\{j\})
  =\sum_{t\ge a}\alpha_t\beta_t,
\]

where `alpha_t` is the conditional post-anchor owner stop mass, so that
`pi_t = p_a alpha_t` and `beta_t = p_a s_t` for owner pre-anchor survival
`p_a` and opponent survival `s_t`.

For every `lambda` with

\[
0<\lambda<m,
\]

there is a date `t >= a` and an actual pure-completion profile `tau` such
that

\[
\Pr_\tau(\text{terminal at }t\text{ is }\{j\})>\lambda,
\tag{1}
\]

the complete post-date live-root tail agrees literally with the source, all
opponents are unchanged, and

\[
d_j(\tau)\le
\frac{p_a-\lambda}{m-\lambda}\,d_j(\sigma)
\le \frac{d_j(\sigma)}{m-\lambda}.
\tag{2}
\]

In particular, along a source sequence with anchored singleton mass tending
to `mu > lambda` and owner debt tending to zero, one obtains cofinally deep
fixed-resolution singleton endpoints whose owner's unrestricted behavioral
debt also tends to zero.

## Proof

For every complete pure stopping time `s`, let `V_s` be player `j`'s payoff
against the fixed opponents when its stopping law is replaced by `s`.  The
pure-time best-response theorem gives

\[
B=\sup_s V_s.
\]

Realize `j`'s source behavioral strategy by its complete stopping law.  Its
payoff is the corresponding mixture of the pure-time values, hence

\[
d=B-U=\sum_s \pi_s(B-V_s).
\tag{3}
\]

Every summand is nonnegative.  Put

\[
e=\sum_{s<a}\pi_s(B-V_s).
\tag{4}
\]

The positive-anchor completion does not have payoff `V_t`: it retains the
source behavior before `a`.  Its payoff and debt are instead

\[
U_j(\tau_t)=\sum_{s<a}\pi_sV_s+p_aV_t,
\qquad
d_j(\tau_t)=e+p_a(B-V_t).
\tag{5}
\]

Let

\[
H=\{t\ge a:\beta_t>\lambda\}
\]

and let `w_H = sum_{t in H} pi_t`.  On `H`, `beta_t <= p_a`; off
`H`, `beta_t <= lambda`.  Moreover
`sum_{t notin H} alpha_t <= 1-w_H/p_a`, because `pi_t=p_a alpha_t`
and the total conditional post-anchor finite-stop mass is at most one.  Hence

\[
m\le \lambda+
\left(1-\frac{\lambda}{p_a}\right)w_H.
\]

Therefore

\[
w_H\ge \frac{p_a(m-\lambda)}{p_a-\lambda}>0.
\tag{6}
\]

From (3),

\[
\sum_{t\in H}\pi_t(B-V_t)\le d-e.
\]

Some `t in H` consequently satisfies

\[
B-V_t\le \frac {d-e}{w_H}.
\tag{7}
\]

Use its pure completion as `tau`.  Equation (1) is the definition of `H`.
Only `j` changes, so its opponents and therefore its unrestricted cap remain
identical:

\[
B_j(\tau)=B_j(\sigma)=B.
\]

Combining (5)--(7), and using `p_a >= m`, gives

\[
\begin{aligned}
d_j(\tau)
&\le e+\frac{p_a-\lambda}{m-\lambda}(d-e)\\
&\le \frac{p_a-\lambda}{m-\lambda}d.
\end{aligned}
\]

Since `p_a <= 1`, this implies the weaker estimate from the original draft.
The behavioral definition gives the prefix and post-date tail equalities.

## Sharpness and limits

The coefficient `(p_a-lambda)/(m-lambda)` is sharp from the supplied data;
the independent review gives a two-player boundary example.  The weaker
`1/(m-lambda)` estimate is convenient when `p_a` is not retained.

The theorem controls only the replaced player's debt.  Other players'
prescribed payoffs and unrestricted caps can change by order one.  Thus it
does not put the target near the minimum fiber and does not by itself produce
support descent, terminal approximation, or a chronological packet.

The result is most promising when the selected singleton player is inactive
at the minimum point.  Then source convergence makes its debt vanish, and the
compression avoids activating that same coordinate.  A consumer still needs
cross-coordinate control or an exact dispatch of any debt transferred to the
other three players.

Minimum provenance does not itself provide that control.  There is a
two-player exact zero-debt source in which both players independently select
date zero or one with probability one half and receive one exactly on a tie.
Compressing one player to date zero preserves its zero debt but creates debt
`1/2` for the other player.  Thus no-new-support cannot be inferred from
whole-law convexity.

## Same-target paid observer under a terminal gap

Assume a terminal exploitability witness of fixed gap `gamma > 0`, and apply
the theorem along the selected minimum chronology with an owner `j` whose
source debt tends to zero.  The compressed target debts `d_j(tau_n)` also
tend to zero.  For large `n`, `j` cannot be the profitable observer supplied
by the gap witness at the literal profile `tau_n`.  Retaining that observer
through the checked pure-time support-pair decoder gives

\[
\exists o_n\ne j,\qquad
\operatorname{Nonempty}
  (\operatorname{QuittingPaidFirstDisagreementRow}
    (r,\tau_n,o_n,\gamma)).
\tag{8}
\]

For Fin4, pass to a subsequence fixing `o_n=o`.  The same actual endpoints
then co-realize:

* singleton stage mass greater than the fixed `lambda`;
* vanishing debt of the singleton owner `j`;
* a full-gap paid row for one fixed observer `o != j`;
* unchanged opponents and a literal copied post-date tail.

Because `j` Quits by the marked date surely in the completion, the two paid
plans cannot first disagree strictly after that date: both would already be
preempted identically.  The first-disagreement row therefore begins no later
than the mark.  The checked division-free live-mass account also supplies a
fixed pre-mark paid reach floor.  This is causal alignment, but not a source
marginal stopping-law atom and not necessarily the marked singleton row.

The public paid-row wrapper currently forgets that its observer was the
profitable coordinate.  A narrow formal adapter should retain it, under the
hypothesis `d_j(tau_n) < gamma`.  This strengthening still does not make a
copied source cap-Nash stack cap-Nash for the changed target.

## Source correspondence

The proof uses the same stopping-law mixture and literal completion machinery
as `exports/FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION.md`, together with the
pure-time representation of unrestricted terminal best responses.  The
relevant project neighborhoods are:

- `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- `UniformEquilibrium/Quitting/Terminal/BehavioralPureTimeBestResponse.lean`;
- `Research/Quitting/SameStageEndpointMonodromy.lean`; and
- `Research/Quitting/FinFourProducerAtlas/Source.lean`.

## Next conjecture-facing question

Consume the co-realized compressed endpoint above.  Prove that its fixed
singleton mass, vanishing owner debt, full-gap nonowner paid row, and literal
tail yield terminal approximants, a uniform-equilibrium payoff, a strict
minimum-fiber support drop, or the existing strong recurrent concentrated
packet.  Recurrent weak endpoints or another named residual are not a
consumer.
