# Review of `RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL`

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`

Reviewed file:
[`notes/CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL.md`](../notes/CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL.md)

Reviewed SHA-256:
`fd49cdcdd7078acfea2a5f1f5d64959ae6552da24547cdf93509461deb0569c1`

## Verdict

**REVISE for one incorrect capacity-scope claim in Section 7.** The new
Section 10 theorem, including the escaping exact clock, bounded total hazard,
positive product/source reach, terminal cap child, distinct paid observer,
and stated nonconsumer, is **PASS**. Sections 1--5 and 8--10 are consistent
with the inspected identities. The required repair does not change the
Section 10 conclusion; it removes a false description of the very broad
finite-block capacity theorem used there.

## Exact Section 10 reconstruction

Let \(A^0\) be the initial literal Quit0 cap. If every recursive root has
positive joint survival, then every player, in particular \(b\), has positive
Continue probability at the new root. Exact root Nash therefore gives

\[
 Q_b(q^n_{-b})\le C_b(q^n_{-b};U_b^n),
\]

with equality when \(h_{n,b}>0\). Since \(d_{n,b}>0\) inductively and
\(s_{n,b}>0\), replacing the tail payoff by its complete cap raises only the
Continue endpoint by \(s_{n,b}d_{n,b}>0\). Thus Continue followed by the old
cap is the unique cap branch, and the recursive clock \(A^{n+1}\) attains the
complete unrestricted cap. The prescribed root mixture equals its Continue
endpoint because either \(h_{n,b}=0\) or the old endpoints tie. Hence

\[
 d_{n+1,b}=s_{n,b}d_{n,b},\qquad
 d_{N,b}=d_{0,b}\prod_{n<N}s_{n,b}.
\]

For the copied-root response, every root-absorbing outcome is unchanged and
only joint Continue exposes the tail improvement. Its gain is exactly
\(c_nd_{n,b}\). The cap is invariant under replacement of \(b\)'s own
strategy, so the residual is

\[
 s_{n,b}d_{n,b}-c_nd_{n,b}
 =h_{n,b}s_{n,b}d_{n,b}=h_{n,b}d_{n+1,b}.
\]

If \(h_{n,b}>0\), old endpoint indifference makes this also the exact support
defect of retaining the copied old root marginal. The orientation and all
three formulas (10.3)--(10.5) are correct.

## Chronological finite block and capacity

For each \(N\), the actual chronological block is

\[
 q^{N-1},q^{N-2},\ldots,q^0,\tau^0,
\]

with displayed values \(U^N,U^{N-1},\ldots,U^0\). At stage \(q^m\), the next
displayed value is \(U^m\), exactly the payoff against which \(q^m\) was
chosen Nash, while the current displayed value is
\(U^{m+1}=F(q^m,U^m)\). This is the correct direction of every Nash--Bellman
edge. Each \(U^m\) is an actual terminal payoff and lies in the canonical
reward box. An arbitrary simplex annotation may be used at the terminal
state.

Therefore the block is accepted by
`QuittingFiniteExactNashBellmanBlock reward
(quittingNashBellmanBox (quittingRewardBound reward))`. The checked
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
gives one upper bound \(K\), uniformly in \(N\), for exactly

\[
 \sum_{n<N}\sum_i h_{n,i}.
\]

Monotone partial sums yield summability. Since every \(h_{n,i}<1\), the
standard positive-product criterion gives

\[
 C_\infty=\prod_n\prod_i(1-h_{n,i})>0.
\]

The finite source reach is \(\prod_{n<N}c_n\ge C_\infty\). Because
\(s_{n,b}\ge c_n\), the lower bound
\(d_{N,b}\ge C_\infty d_{0,b}\ge C_\infty\gamma\) follows. No exchange of
the reverse chronological order is used.

## Terminal cap child and paid row

The clock \(A^N\) Quits exactly at calendar date \(N\) in \(\tau^N\).
Updating \(b\) to it therefore makes \(\zeta^N\) terminal by date \(N\),
attains the full behavioral cap, gains \(d_{N,b}\), and kills \(b\)'s debt
exactly.

The terminal witness at \(\zeta^N\) selects \(j_N\ne b\) with debt at least
\(\Gamma\). Against opponents that surely absorb by date \(N\), every pure
time after \(N\) is payoff-equivalent to Never, while time \(N\) remains a
distinct simultaneous-quit endpoint. Hence the unrestricted pure-time cap is
attained in \(\{0,\ldots,N,\mathrm{Never}\}\).

Choose a prescribed pure-time component with value no greater than the
prescribed expectation. Comparing it with the cap maximizer retains the full
\(\Gamma\) gap. If either witness were strictly after \(N\), it is
payoff-equivalent to Never; positivity of the gap therefore forces the first
disagreement cut to be at most \(N\). The ordinary paid-row constructor then
gives

\[
 \Gamma\le 2M\,\operatorname{OpponentLiveMass},
\]

so the stated \(\Gamma/(2M)\) lower bound is correct for \(M>0\). This is a
literal two-edge chronology, but the owner cap update changes all of \(b\)'s
prefix actions and need not preserve the other players' old root Nash
inequalities. The note correctly stops short of calling it a Bellman return.

## Required correction: Section 7 misstates the capacity hypotheses

Section 7 says that the checked finite exact-block capacity requires the
continuation payoff to satisfy punishment floors and the states to lie in a
punishment-floor reachable relation. That is false for the capacity theorem
actually cited and used in Theorem 10.2.

In
`UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`,
`QuittingFiniteExactNashBellmanBlock reward carrier` requires only:

1. a positive finite horizon;
2. membership of every displayed annotation in the supplied carrier; and
3. literal exact Nash--Bellman edges.

In
`UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`,
the counterexample-side theorem takes the carrier to be the canonical
`quittingNashBellmanBox (quittingRewardBound reward)`. It has no punishment-
floor or reachability hypothesis. Full normality is derived internally in
the proof of the opposite unbounded-capacity arm; it is not a field required
of each supplied block.

Accordingly the paragraph beginning “For an arbitrary nontrivial root” and
the later statement that only the all-Continue identity stall is accepted by
the checked capacity should be deleted or rewritten to distinguish some
other floor-admissible capacity notion. Theorem 10.2 already applies the
broad canonical-box theorem correctly, so its proof and conclusion survive
unchanged. The duplicate equation label `(7.2)` is also worth renumbering but
is presentation only.

## Other checks

- The nested positive-part recurrence in (2.5) is valid because every
  survival factor and exercise premium is nonnegative.
- The collision and wrong-owner singleton estimates (3.3)--(3.6) have the
  correct direction; their summability follows from the total-debt
  telescope.
- With at least two persistent debtors, choosing a different persistent
  coordinate for each marginal gives summability of every hazard. With one
  persistent debtor, it gives exactly the three outsider hazards and no
  unjustified bound on the owner's hazard.
- The all-Continue stall example has a terminal Nash singleton and therefore
  is only a local recursion falsifier, as stated.
- The maximal-drop limit correctly distinguishes closedness from lower
  hemicontinuity. Its fixed limiting root is only approximate at prelimit
  sources, and the note retains that scope.
- The terminal cap child does not regenerate stationarity, a singleton cap
  pin, a forward spine, or a renewable rank. No such conclusion is claimed.

After the Section 7 scope correction, I have no mathematical objection to
the note.

## Delta review of the repaired note

Rechecked exact SHA-256
`3823bb3e816de7d3328b0a82045dae42daae9f3cd3a937b7b50bf7a3370052ee`.

**PASS.** Section 7 now states the canonical-box capacity hypotheses
correctly: actual payoff-box membership and exact Nash--Bellman edges suffice,
while punishment floors are reserved for the separate infinite floor-orbit
and charged-return consumers. The all-Continue stall is correctly described
as a floor-admissible zero-charge edge rather than as the only root accepted
by the capacity theorem, and the chronology tag is repaired to `(7.4)`.

The Section 10 clock transport, bounded-capacity/product proof, terminal cap
child, full-gap paid row, and nonconsumer statement are unchanged in
mathematical content from the version audited above. I have no remaining
objection at this hash.
