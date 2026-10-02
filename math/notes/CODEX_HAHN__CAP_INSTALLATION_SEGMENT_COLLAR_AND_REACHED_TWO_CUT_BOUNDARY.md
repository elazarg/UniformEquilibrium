# The structured cap-installation segment stays uniformly off minimum

Author: `CODEX_HAHN`

## Status

**Exact ordinary mathematics; global collar strengthening and exact consumer
boundary, not Lean-checked.**  The private stopping-law segment which installs
the structured tropical source's Quit0 cap never approaches the global
minimum fibre.  Its named cap coordinate is literally constant, whereas the
same coordinate has a full positive-minimum margin at every global minimum.
Compactness upgrades this coordinate separation to one uniform total-debt
excess along the whole moving segment.

At every proper point bounded away from the cap endpoint, an arbitrary exact
payoff-tail root spends a fixed amount of total debt.  If the resulting exact
prefix approaches the minimum fibre with positive joint survival, the
off-minimum paid tail is literally reached.  Nevertheless the most immediate
two-cut block is exhausted by its already-known off-minimum-exit arm: after
the cap-mixture row, stationarity returns exactly to the original off-minimum
source.  Thus this gives a sharper source-matched split, but not a terminal or
renewable consumer.

## Question

Can the positive-minimum cap collar charge the outsider Nash loss caused by a
horizontal cap installation, so that a structured off-minimum paid source
either returns through an accepted exact chronology or yields a renewable
rank decrease?

The collar controls the entire installation segment and produces a charged
exact prefix.  It does not by itself charge the horizontal seam or prevent
the two-cut endpoint from returning to the same off-minimum source.

## 1. Abstract whole-segment collar

Let \(I\) be finite, let \(r\) be a bounded quitting reward table, and let
\(\mathcal K_r\) be its compact terminal-semantic carrier.  For
\(X=(U,B)\in\mathcal K_r\), write

\[
 d_i(X)=B_i-U_i,\qquad D(X)=\sum_i d_i(X).
\]

Assume

\[
 D_*:=\min_{X\in\mathcal K_r}D(X)>0,
 \qquad
 \mathcal F:=\{X\in\mathcal K_r:D(X)=D_*\}.
\tag{1}
\]

Fix a player \(b\), put \(s_b=r_b(\{b\})\), and assume the minimum singleton
margin

\[
 B_b(Z)\ge s_b+D_*\qquad(Z\in\mathcal F).
\tag{2}
\]

Let \(\sigma_n\) be actual behavioral profiles and let \(A_n\) be complete
behavioral cap responses for player \(b\).  Suppose

\[
 d_b(\sigma_n)\ge\gamma>0,
 \qquad
 B_b(\sigma_n)\longrightarrow s_b.
\tag{3}
\]

For \(t\in[0,1]\), form the executable private stopping-law mixture

\[
 \sigma_n^t
 =\sigma_n\bigl[b\leftarrow
   (1-t)\operatorname{Law}(\sigma_{n,b})
    +t\operatorname{Law}(A_n)\bigr],
\tag{4}
\]

and write \(X_n^t=\operatorname{Sem}(\sigma_n^t)\).

### Theorem 1.1

For every \(n\) and \(t\),

\[
 B_b(X_n^t)=B_b(\sigma_n),
 \qquad
 d_b(X_n^t)=(1-t)d_b(\sigma_n).
\tag{5}
\]

Let the asymptotic segment cluster be

\[
 \mathcal C_\infty
 =\bigcap_{N\ge0}
   \overline{\{X_n^t:n\ge N,\ 0\le t\le1\}}.
\tag{6}
\]

Then \(\mathcal C_\infty\) is nonempty and compact, and every
\(Y\in\mathcal C_\infty\) satisfies

\[
 B_b(Y)=s_b,
 \qquad
 \inf_{Z\in\mathcal F}|B_b(Z)-B_b(Y)|\ge D_*.
\tag{7}
\]

In particular \(\mathcal C_\infty\cap\mathcal F=\varnothing\).  Hence there
is a number \(\delta_{\mathrm{seg}}>0\) such that, for every sufficiently
large \(n\) and every \(t\in[0,1]\),

\[
 \boxed{D(X_n^t)\ge D_*+\delta_{\mathrm{seg}}.}
\tag{8}
\]

### Proof

Changing player \(b\)'s own prescribed stopping law leaves its opponents
literal.  Its unrestricted cap is therefore identical at every point of the
segment.  Prescribed payoff is affine in that private mixture, and the
endpoint \(A_n\) pays exactly the common cap.  This proves (5).

The carrier is compact.  Thus the nested nonempty compact tail closures in
(6) have nonempty compact intersection.  Every convergent choice
\(X_{n_k}^{t_k}\to Y\), with \(n_k\to\infty\), has
\(B_b(Y)=s_b\) by (3) and (5).  Equation (2) gives (7), so the two compact
sets \(\mathcal C_\infty\) and \(\mathcal F\) are disjoint.

Every point of \(\mathcal C_\infty\) belongs to the carrier and is not in
the minimum fibre, hence has debt strictly greater than \(D_*\).  Continuity
of \(D\) and compactness give

\[
 \epsilon=\min_{Y\in\mathcal C_\infty}(D(Y)-D_*)>0.
\]

If the eventual uniform statement failed with, say,
\(\delta_{\mathrm{seg}}=\epsilon/2\), there would be
\(n_k\to\infty\), \(t_k\in[0,1]\), and a convergent subsequence whose limit
lies in \(\mathcal C_\infty\) and has debt at most
\(D_*+\epsilon/2\), a contradiction.  This proves (8).

The constant in (8) is compactness-based and need not have an explicit
formula in terms of \(D_*\).  The explicit part is the cap-coordinate gap
(7).

## 2. A fixed charged exact prefix at every proper segment point

Choose any fixed \(0<\lambda<1\) and put

\[
 t_*=1-\lambda,
 \qquad
 g=\lambda\gamma,
\]

\[
 c_0=\min\left\{\frac g2,\frac{g^2}{16M}\right\},
 \qquad
 a_0=\min\left\{1,\frac g{16M}\right\},
\tag{9}
\]

where every reward and prescribed-payoff coordinate lies in \([-M,M]\) and
\(M>0\).  By (5),

\[
 d_b(X_n^{t_*})\ge g.
\tag{10}
\]

Since \(B_b(X_n^{t_*})=B_b(\sigma_n)\to s_b\), eventually

\[
 |B_b(X_n^{t_*})-s_b|\le g/4.
\tag{11}
\]

Let \(q_n\) be any exact independent product root Nash against the literal
prescribed payoff \(U(X_n^{t_*})\), and put

\[
 Y_n=\operatorname{Prefix}(q_n,X_n^{t_*}),
 \qquad c_n=\Pr_{q_n}(\text{all Continue}).
\tag{12}
\]

The reviewed fixed-cap-pin theorem applies to (10)--(11), uniformly over the
choice of exact root.  Therefore

\[
 \boxed{
 D(X_n^{t_*})-D(Y_n)\ge c_0,
 \qquad
 \operatorname{Abs}(q_n)\ge a_0.}
\tag{13}
\]

This is an actual exact Nash--Bellman predecessor edge from the tail payoff
to the prefixed payoff.  It is not the horizontal cap response.

After a subsequence there are two relevant cases.

1. If \(D(Y_n)\ge D_*+\epsilon\) for some fixed \(\epsilon>0\), the exact
   child remains uniformly off minimum.  The old tail cap response is
   reset/shifted through later positive-survival prefixes as a transported
   feasible response, but no attainment of the new prefixed cap is asserted
   and the singleton cap pin (11) is not preserved.  Thus (13) cannot simply
   be iterated without a horizontal reinstall; this is the existing
   escaping-cap-clock branch.
2. If \(D(Y_n)\to D_*\), the literal prefixed profiles are a near-minimum
   source family.  If also \(c_n\ge\eta>0\), their exact first root reaches
   the off-minimum tail \(\sigma_n^{t_*}\) with probability at least
   \(\eta\).  Player \(b\)'s cap-attaining response at that tail extends
   through the fixed prefix as a source-attached feasible behavioral response
   of gain at least \(\eta g\); it need not attain the complete cap of the
   prefixed profile.  If the response endpoint also approaches the minimum
   fibre, the pair enters the standard minimum-response-chord geometry; any
   support/source regeneration still requires the atom and maximal-support
   hypotheses of the existing handoff.  If the endpoint does not approach
   the minimum fibre, it is an off-minimum paid endpoint.  Neither alternative
   is a new terminal consumer.

When \(c_n\to0\), the reached-tail floor disappears.  That is the existing
zero-survival/unique-sure branch, not a reached two-cut source.

## 3. The reached two-cut block has a predetermined off-minimum exit

Now specialize to the structured tropical source.  Each \(\sigma_n\) is
stationary, and \(A_n\) is literal Quit at date zero.  At any fixed proper
parameter \(0<t<1\), the segment profile \(\sigma_n^t\) has the following
exact form:

- at its first date, player \(b\) uses the mixture of Quit0 with its original
  stationary action;
- conditional on joint Continue at that date, the private Quit0 branch has
  been excluded; and
- by memorylessness of every original stationary coordinate, the literal
  continuation is exactly \(\sigma_n\) again.

Consequently, in the near-minimum positive-survival case of Section 2, take
the root \(q_n\) as marked row zero, the first row of
\(\sigma_n^{t_*}\) as the entry block row, and the next suffix as exit.  Then

\[
 \operatorname{entryCut}=1,
 \qquad
 \operatorname{exitCut}=2,
\tag{14}
\]

the entry is reached with probability \(c_n\ge\eta\), and the one-row block
has total marginal hazard at least \(t_*>0\), since the cap branch makes
player \(b\) Quit there with probability at least \(t_*\).  But the exit
suffix is literally

\[
 \operatorname{suffix}_2(q_n::\sigma_n^{t_*})=\sigma_n.
\tag{15}
\]

The structured source already satisfies

\[
 D(\sigma_n)\ge D_*+\delta
\tag{16}
\]

for one fixed \(\delta>0\) on a tail.  Therefore the checked positive-minimum
two-cut dichotomy must be instantiated at a hazard scale compatible with
this exit excess.  For example, put

\[
 h_0=\min\left\{t_*,\frac12\log\left(1+\frac{2\delta}{D_*}\right)\right\}>0.
\tag{17}
\]

The one-row total marginal hazard is at least \(t_*\), hence at least
\(h_0\), while

\[
 \frac{e^{h_0}-1}{2}D_*\le\delta.
\tag{18}
\]

Thus the theorem's off-minimum-exit alternative is already true by
(15)--(18).  It is not forced to return its paid-splice arm.

This identifies the exact failure of the tempting source adapter:

\[
 \boxed{
 \text{near-minimum exact root reaches the cap segment}
 \quad\Longrightarrow\quad
 \text{a valid two-cut block whose exit is the original off-minimum port}.}
\tag{19}
\]

The block is genuine and source matched.  Its consumer output is not new.

## 4. Law displacement is macroscopic but unsigned

Let \(\nu_n^0\) and \(\nu_n^1\) be the complete ordinary terminal laws of
\(\sigma_n\) and its cap child \(\sigma_n[b\leftarrow A_n]\).  Private
mixture gives the exact affine law

\[
 \nu_n^t=(1-t)\nu_n^0+t\nu_n^1.
\tag{20}
\]

If the cap response gains at least \(\gamma\), bounded-payoff duality gives,
under the total-variation convention
\(\|\mu-\nu\|_{\mathrm{TV}}=\sup_A|\mu(A)-\nu(A)|\),

\[
 \|\nu_n^1-\nu_n^0\|_{\mathrm{TV}}
 \ge \frac{\gamma}{2M}.
\tag{21}
\]

Similarly, a fixed outsider pure-response gap which changes by \(\xi>0\)
across the installation forces a fixed operational displacement of the
changed stopping law, with the standard constant obtained from the
\(4M\)-Lipschitz gain estimate.

These are metric lower bounds, not signed chronological charge.  A finite
response cycle may make macroscopic law moves in alternating directions, so
their total variations do not telescope.  The exact two-clock/move-to-front
regressions realize this failure at global minimum zero.  Positive global
minimum supplies (7)--(8), but it does not give a sign to (19).

## 5. Exact remaining condition

The collar route would become a consumer if one could prove either of the
following additional statements for the literal source genealogy.

1. A positive-survival exact prefix whose child approaches the minimum fibre
   forces the cap-response endpoint to remain on that fibre with preservation
   of the already killed debt coordinates.  Then the existing finite support
   handoff is renewable.
2. Returning from the fixed off-minimum exit (15) to a minimum-attached child
   pays a signed Nash--Bellman or punishment-floor seam bounded below in
   terms of \(\delta_{\mathrm{seg}}\), rather than merely the unsigned law
   distance (21).

Without one of these, the whole-segment collar and the reached two-cut block
end at the same off-minimum paid-port/source-reentry component.

## Source audit

The structured stationary source, fixed Quit0 cap, positive debt, stationary
self-tail, source ancestry, and off-minimum excess are in
`exports/FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md`.

The minimum singleton margin is
`minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.
Compactness of the carrier and continuity of total debt are in the terminal
semantic carrier/equality-stratum modules named by that export.

Stopping-law mixture affinity and complete-cap convexity are in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`.
The fixed root expenditure (13) is the reviewed theorem in
`exports/FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md`.

The reached-block consumer is
`QuittingUniformlyReachedPostMarkTwoCutBlock.finFour_offMinimum_or_exists_paidSplice`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean`,
documented in
`formalized/POSITIVE_MINIMUM_TWO_CUT_COERCIVITY_AND_PAID_SPLICE.md`.

The transported feasible-response reset/shift and positive-/zero-survival
boundaries are in
`exports/FIN4_POSITIVE_SURVIVAL_ESCAPING_EXACT_CAP_CLOCK.md` and
`exports/FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET.md`.

## Boundary tests and nonclaims

1. **The segment collar uses the genuine global minimum.**  A cap separation
   from one selected zero-debt or low-debt point does not prove (7)--(8).
2. **The response endpoint is included.**  At \(t=1\), player \(b\)'s debt
   is zero, but its cap coordinate is still \(s_b\) in every segment limit;
   the endpoint remains off minimum.
3. **No explicit total-debt collar follows from coordinates alone.**  The
   existence of \(\delta_{\mathrm{seg}}\) uses compactness.  It is not
   asserted to equal \(D_*\).
4. **The segment row is not exact Nash.**  At every proper point it retains
   positive \(b\)-debt.  Its large absorption cannot be inserted into an
   exact Nash--Bellman chronology without changing the row.
5. **The two-cut theorem is inclusive.**  Since its off-minimum endpoint arm
   already holds, it need not select the paid-splice arm.
6. **The exact child is not automatically renewable.**  After prefixing, the
   named cap is a shifted tail cap and need not stay near the singleton
   reward.  The fixed expenditure (13) is therefore one-step.
7. **Law distance is not a potential.**  Equation (21) gives no orientation
   around a horizontal response cycle.
8. No terminal approximate Nash profile, source-reprojected charged return,
   renewable finite rank, or uniform-equilibrium payoff is proved.

## Lean handoff

The narrow reusable declarations would be:

```text
capResponseSegment_ownerCap_eq
capResponseSegment_ownerDebt_eq_oneSub_mul
minimumSingletonMargin_capResponseSegment_cluster_disjoint
eventually_capResponseSegment_debtSum_ge_min_add
tropicalQuitNowSegment_suffix_one_eq_source
nearMinimumPrefix_capSegment_twoCut_exit_eq_originalSource
```

The first two should reuse the existing stopping-law mixture identities.  The
cluster theorem should be stated for the tail-limit set (6), not for an
arbitrary union of segment images.  The tropical suffix theorem must use the
literal stationary source and Quit0 endpoint; it is false for a general cap
response.
