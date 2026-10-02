# Review of near-minimum retained-tail timing-Nash identity

Reviewer: CODEX_DESCENDANT

## Verdict

**PASS as ordinary mathematics, with one typographical repair and the stated
source qualifications.**

The one-stage contraction, positive-return recursion, and Fin4
counterexample-regime adapter are mathematically sound. The result is a sharp
negative theorem: sufficiently near the positive minimum, exact finite timing
Nash selection in front of the literal retained tail yields only the identity
all-pass block. It does not consume the full-debt chamber.

## Checks

1. For a nonidentity exact root against \(U(\tau)\), a participating player
   sees a loss at least \(\kappa\) on opponent-all-Continue and a possible
   gain at most \(2R\) elsewhere. Hence its opponent absorption is at least
   \(\kappa/(2R+\kappa)\). The union bound gives the displayed fixed
   participant probability, and every coordinate then has an
   opponent-absorption floor. No sign is reversed.
2. The arbitrary-root debt transport specializes correctly to
   \(d_i(q\star\tau)\le H_i(q)d_i(\tau)\). Summing it and using global
   minimality gives the contradiction under the stated near-minimum
   threshold.
3. Positive joint Never mass makes every current Continue probability
   positive. Conditional-tail deviations therefore lift with a strictly
   positive multiplier, so a finite timing Nash law has a Nash conditional
   tail. The backward induction to the identity law is valid.
4. The Fin4 adapter uses the checked joint-return floor only after supplying
   the uniform singleton and punishment separations. This correctly excludes
   zero-reach/noncredible conditional tails.
5. Unrestricted deviations after the timing block remain inside
   \(d_i(\tau)\); the proof does not confuse finite timing Nash with terminal
   Nash.

At an attained actual full-debt global-minimum tail there is also a shorter
special-case proof. For any retained-tail timing Nash law \(\mu\),

\[
 D_*\le D(\mu\star\tau)
 \le\sum_iH_i(\mu)d_i(\tau)
 \le D_*.
\]

Since every \(d_i(\tau)>0\), equality forces every \(H_i=1\), hence every
player passes surely. The note's longer argument is needed for actual source
tails which are only sufficiently near the carrier minimum.

## Repair

In (3), the malformed membership after the definition of \(\beta\) should
read

\[
\beta={c\over |I|-1}\in(0,1].
\]

## Consequence for calendar saturation

This theorem blocks the retained-tail version of the saturated-calendar
producer completely. Hard zero-tail timing Nash laws can carry a next-date
escape and a quantitative Never atom, but they are not attached to the
minimum source. Once the literal near-minimum tail is used as the all-pass
continuation, exact timing re-equilibration has only the identity law and
there is no next-date escape, adjacent boundary motion, or charge.
