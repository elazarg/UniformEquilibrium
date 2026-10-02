# Local periodic obstructions after the face-enlargement audit

Source derivation: `../FACE_ENLARGE_FOLLOWUP.md`

## Current status

The derivation contains three distinct mathematical candidates.

1. A fixed lower bound on exploitability for a small periodic product profile
   whose actual phase payoffs stay uniformly above every own singleton reward.
2. A pre-equilibrium algebraic obstruction: prescribed period closure near the
   own-singleton vector forces a homogeneous simplex-LCP direction.
3. A period-length-free Abel estimate and the corresponding proposed
   two-clock residual consumer.

The first result and the scalar Abel estimate check directly.  The second
result is the most conjecture-facing: unlike the earlier fixed-period no-go,
it assumes prescribed Bellman closure rather than terminal approximate Nash,
so it genuinely obstructs a proposed producer before reaching the desired
semantic endpoint.  The full two-clock adapter still requires an independent
audit against the repository's exact residual definitions.

None of these results constructs a chronology from the strict face blocker.
They instead rule out local regularization at both natural anchors and sharpen
the remaining producer to a macroscopic excursion/return or a minimum-fiber
support exit.

## Minimum-tube Never barrier

Let `I` have cardinality `n`, let `s_i=r_i({i})`, and periodically repeat `K`
product roots with Quit probabilities `q_{k,i}`.  Let `u_k` be the actual
terminal payoff from phase `k`, let `R` bound every absolute terminal reward,
and assume

\[
u_{k,i}\ge s_i+\eta\quad(k,i),
\qquad
\max_{k,i}q_{k,i}
\le \frac{\eta}{2(n-1)(\eta+2R)}.
\]

Assume joint survival and every player-deleted survival contract strictly over
one turn.  If `v_{k,i}` is player `i`'s payoff after deviating to Never and
`G_{k,i}=v_{k,i}-u_{k,i}`, direct subtraction of the Bellman equations gives

\[
\begin{aligned}
G_{k,i}={}&\beta_{k,-i}G_{k+1,i}
+q_{k,i}\beta_{k,-i}(u_{k+1,i}-s_i)\\
&+q_{k,i}\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
P_{k,-i}(T)\bigl(r_i(T)-r_i(T\cup\{i\})\bigr).
\end{aligned}
\]

The reward bound and small-root hypothesis imply

\[
G_{k,i}\ge\beta_{k,-i}G_{k+1,i}+\frac\eta2q_{k,i}.
\]

After iteration, deleted-clock contraction removes the bounded remainder.
Joint absorption gives

\[
\sum_i\sum_t W_{t,-i}q_{t,i}\ge1.
\]

Hence some player's Never gain is at least

\[
\boxed{\operatorname{Expl}\ge\frac{\eta}{2n}}.
\]

For Fin4, the checked uniform minimum-fiber singleton separation supplies a
fixed `delta>0`.  Taking `eta=delta/2` shows that sufficiently small periodic
roots whose actual phase payoffs remain in the minimum tube have
exploitability at least `delta/16`, provided all deleted clocks contract.

The deleted-clock assumption is essential: a unique active player can be
disciplined by slower clocks which vanish in the limit.

## Solo-anchor prescribed-closure obstruction

Let

\[
M_{ij}=r_i(\{j\})-r_i(\{i\}).
\]

For a possibly varying-period family, put

\[
A_h=\sum_{k,j}q^h_{k,j},
\qquad
Q_{h,j}=\sum_kq^h_{k,j}.
\]

Assume `A_h>0`, the largest root hazard tends to zero, all phase annotations
converge uniformly to the own-singleton vector `s`, and the sum of the
prescribed Bellman residuals is `o(A_h)`.  First-order expansion gives

\[
M Q_h=o(A_h).
\]

The accumulated collision error is `o(A_h)` even when the period varies,
because

\[
\sum_k\left(\sum_jq^h_{k,j}\right)^2
\le n\max_{k,j}q^h_{k,j}\,A_h.
\]

After normalizing `lambda_h=Q_h/A_h` and taking a subsequence,

\[
\lambda_h\to\lambda\in\Delta(I),
\qquad
M\lambda=0.
\]

Thus prescribed payoff-period closure near the solo vector already forces a
homogeneous simplex-LCP solution.  No terminal approximate-equilibrium
hypothesis or debt-complementarity argument is used.  In the Fin4 hard
residual this conclusion is forbidden.

This is the precise valid version of the slogan:

> Near the solo-normalized anchor, prescribed payoff-period closure forces a
> forbidden homogeneous singleton-LCP direction even though an abstract debt
> circulation may close.

## Scale-free periodic Abel estimate

For one turn `a_0,...,a_{K-1}`, decreasing multiplicative weights
`w_0=1`, `w_{k+1}=w_k c_k`, and `q=w_K<1`, put

\[
R=\sum_{k<K}a_k,
\qquad
E=\max_{0\le m\le K}\left|\sum_{k<m}a_k\right|.
\]

Summation by parts on one turn followed by the geometric repetition gives

\[
\boxed{
\left|\sum_{t\ge0}W_ta_{t\bmod K}\right|
\le E+\frac{|R|}{1-q}.}
\]

The estimate has no explicit factor `K`.  Taking the maximum prefix error
over all cyclic rotations makes it phase-independent.  It should replace the
fixed-period `K(A+B)` estimate in any long-word two-clock consumer.

The proposed terminal-debt bound applies this estimate to the prescribed
Bellman residual under both joint and deleted-player clocks and to the direct
debt residual under the deleted-player clock.  That composition is plausible
from the existing two-clock identity but has not been independently checked
here.

## Consequence for the producer

Two local anchors are excluded:

* staying in the minimum tube creates a fixed Never gain; and
* collapsing toward the solo-normalized vector with relative prescribed
  closure creates a forbidden homogeneous direction.

Therefore a successful chronological realization of the finite toggle data
must either make a macroscopic payoff excursion and return, use a singular
deleted-clock regime, or produce an actual minimum-fiber endpoint satisfying
the no-new-support/vanished-debtor rank passport.  The derivation does not
produce any of these outputs.

## Requested checks

1. Audit the two-clock use of the scale-free Abel estimate against the exact
   signs and residual definitions in the chronological debt identity.
2. Test the solo-anchor theorem with varying periods, nonuniform phase
   annotations, and roots with a single dominant hazard scale.
3. Determine whether the strict face blocker can force either a macroscopic
   excursion entrance or one of the semantic rank-passport inequalities.

