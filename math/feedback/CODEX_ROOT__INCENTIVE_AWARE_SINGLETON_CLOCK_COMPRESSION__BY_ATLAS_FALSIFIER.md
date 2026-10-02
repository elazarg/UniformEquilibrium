# Adversarial review of incentive-aware singleton clock compression

Reviewer: `ATLAS_FALSIFIER`

## Verdict

The corrected anchored averaging theorem in
`CODEX_ROOT__INCENTIVE_AWARE_SINGLETON_CLOCK_COMPRESSION__BY_STRENGTHENER`
is mathematically valid.  Its sharper coefficient

\[
 d_j(\tau_t)\le {p_a-\lambda\over m-\lambda}d_j(\sigma)
\]

survives the positive-anchor case, and the two-player example really does
refute any automatic no-new-support conclusion for the other coordinates.
Under a terminal exploitability gap, the same compressed endpoint also
carries a full-gap paid first-disagreement row for an observer distinct from
the compressed owner, with first-disagreement date no later than the forced
singleton deadline.

These results are exportable as a producer package after the localized
distinct-observer wrapper is supplied.  They do **not** consume the weak
concentrated-singleton atlas node.  In particular, the new paid row and the
vanishing owner debt are not preserved by the pure-root purification used to
construct the source-matched toggle cycle and response square.

## Sources checked

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- the unrestricted pure-time cap representation in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingContinuationBestResponseValue_update_self`;
- `HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` and
  `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`;
- `QuittingPaidFirstDisagreementRow` and
  `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- the actual pure-root sibling construction used in
  `ATLAS_FALSIFIER__CONCENTRATED_SINGLETON_FULL_GAP_TOGGLE_CYCLE`.

## 1. Anchored stopping-law identity

Let \(\pi_s\) be the owner's complete stopping-law mass, including the
Never atom, and put

\[
 p_a=\Pr(T_j\ge a),\qquad B=\sup_s V_s,\qquad
 g_s=B-V_s\ge0.
\]

The source debt is the bounded stopping-law expectation

\[
 d=\sum_{s\in\mathbb N\cup\{\infty\}}\pi_sg_s.
\]

The completion \(\tau_t\) retains exactly the old atoms below \(a\), and
places all remaining mass \(p_a\) at \(t\).  Its stopping law is therefore

\[
 \Pr_{\tau_t}(T_j=s)=
 \begin{cases}
 \pi_s,&s<a,\\
 p_a,&s=t,\\
 0,&\text{otherwise}.
 \end{cases}
\]

The post-\(t\) behavioral tail may be copied literally, but is unreachable
under the prescribed completion.  Since only \(j\)'s strategy changes, its
opponents and hence its unrestricted behavioral cap are unchanged.  Thus,
with \(e=\sum_{s<a}\pi_sg_s\),

\[
 U_j(\tau_t)=\sum_{s<a}\pi_sV_s+p_aV_t,
 \qquad
 d_j(\tau_t)=e+p_ag_t.
\]

This is the exact correction to the false positive-anchor identity
\(U_j(\tau_t)=V_t\).  It is legal for arbitrary behavioral strategies: the
argument passes through complete stopping laws, not a stationary or
finite-support reduction.

## 2. The high-survival bound

Write \(s_t\) for unconditional opponent survival through \(t\),
\(\beta_t=p_as_t\), and \(\alpha_t=\pi_t/p_a\).  Then

\[
 m=\sum_{t\ge a}\alpha_t\beta_t,
 \]

and \(m>\lambda>0\) implies \(p_a\ge m>\lambda\).  For

\[
 H=\{t:\beta_t>\lambda\},\qquad
 w_H=\sum_{t\in H}\pi_t,
\]

one has

\[
 m\le p_a\sum_H\alpha_t+\lambda\sum_{H^c}\alpha_t
 \le \lambda+{p_a-\lambda\over p_a}w_H.
\]

Hence

\[
 w_H\ge {p_a(m-\lambda)\over p_a-\lambda}>0.
\]

The regret carried by \(H\) is at most \(d-e\), so some \(t\in H\)
satisfies \(g_t\le(d-e)/w_H\).  Therefore

\[
 d_j(\tau_t)
 \le e+{p_a-\lambda\over m-\lambda}(d-e)
 \le {p_a-\lambda\over m-\lambda}d.
\]

The last inequality has the correct direction because \(p_a\ge m\), so the
coefficient is at least one.  The Never mass causes no gap: it can only add
nonnegative regret to \(d-e\) and is not needed in the selected finite set
\(H\).

The boundary construction in the strengthening review attains the coefficient
from these data.  Its use of the symbol \(\lambda\) both for the opponent's
Never probability and for the strict threshold is harmless when interpreted
at the limiting threshold; at equality, the date-one completion lies outside
\(H\) because the definition uses \(>\lambda\).

## 3. The no-new-support regression is genuine

In the two-player table paying each player one exactly on the joint coalition
and zero otherwise, let each player independently choose date zero or date
one with probability one half.  Against either player, the two pure dates
both pay \(1/2\), and every behavioral stopping law is a mixture of pure
times, so the profile is an exact terminal Nash profile with debt vector
\((0,0)\).

Compressing player \(j\) to date zero leaves its cap and payoff equal to
\(1/2\).  The opponent's prescribed mixture still pays \(1/2\), but its
date-zero deviation pays one, so the new debt vector is
\((0,1/2)\), up to coordinate order.  Thus even compression of an inactive
owner at a global-minimum source can create a new active coordinate.  This
is an all-behavior counterexample to no-new-support, not merely a convexity
warning.

## 4. The near-minimum-or-paid-target dispatch

The sequence-level dispatch in the strengthening review is correct with the
following scope.  If the minimum/no-entry convergence fails, then after a
subsequence either

1. \(D(\tau_n)\ge D_*+c\), or
2. one fixed coordinate outside the old active set has
   \(d_q(\tau_n)\ge c\).

Since \(D(\sigma_n)\to D_*\) and both source and target owner debts vanish,
the first case gives a fixed nonowner whose debt increase is bounded below;
the second case gives one directly.  Pure-time cap approximation plus the
prescribed stopping-law average then gives a paid first-disagreement row of
any fixed gain below that debt floor.  Conversely, the first arm alone gives
strict support descent only if an old active coordinate is separately shown
to vanish.  Thus this is an honest endpoint dichotomy, not an exhaustive
atlas consumer.

## 5. Terminal-gap wrapper and deadline alignment

The stronger terminal-gap statement is valid.  The proof of
`HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` retains
the observer selected by the exploitability witness.  If
\(d_j(\tau_n)<\gamma\), that observer cannot be \(j\): an actual deviation
gaining \(\gamma\) would force \(d_j(\tau_n)\ge\gamma\).  Applying the same
support-pair construction with the observer retained gives

\[
 \exists o\ne j,\quad
 \operatorname{Nonempty}
  (\operatorname{QuittingPaidFirstDisagreementRow}
       (r,\tau_n,o,\gamma)).
\]

Only a narrow localized wrapper is missing from the public Lean interface;
the mathematics is already present in the checked proof.

Moreover, under \(\tau_n\), player \(j\) stops no later than the completion
date \(t_n\) almost surely.  For \(o\ne j\), all pure stopping plans strictly
after \(t_n\), including Never, therefore have the same payoff.  A positive
pure-time pair cannot have both entries after \(t_n\), so its first
disagreement is at most \(t_n\).  This proves the advertised deadline
alignment without claiming that the paid row occurs exactly at the singleton
date.

## 6. Why the paid endpoint does not attach to the response square

The compressed endpoint \(\tau_n\) has a mixed product root at the marked
date: the owner \(j\) Quits surely, but the other three coordinates retain
their source actions.  The horizontal toggle-cycle adapter first replaces
those coordinates by pure actions, producing siblings \(\rho_A\).  That
operation changes opponents of the paid observer \(o\ne j\), so it can change
both pure-time values in the paid row and the observer's unrestricted cap.
It also changes opponents of \(j\), so the small owner debt need not survive.
The two-player regression above demonstrates that this kind of witness switch
can be order one.

Therefore neither implication is valid:

\[
 \text{paid row at }\tau_n
 \Longrightarrow
 \text{same paid row at a pure sibling }\rho_A,
\]

\[
 d_j(\tau_n)\to0
 \Longrightarrow
 d_j(\rho_A)\to0.
\]

There is a weaker exact averaging observation.  For a fixed pure-time pair of
observer \(o\), its payoff difference is multi-affine in the other players'
marked-root probabilities.  Hence a positive difference at \(\tau_n\) is at
least as large at some pure endpoint of the opponents' root cube.  Changing
\(o\)'s own prescribed root afterward does not affect those two deviation
payoffs.  Thus one can find a pure nonempty sibling, necessarily containing
the sure-quitting owner \(j\), that retains the paid **pair**.  This endpoint
need not be the singleton sibling, need not lie on the eventual toggle cycle,
and need not retain small owner debt.  It is therefore a potentially useful
same-cube attachment, but not a consumer or a well-founded transition.

The response-square reduction from an exceptional toggle cycle has the same
limitation.  Its square corners are pure siblings selected by cube geometry;
the averaging endpoint carrying the paid pair is not forced to be one of
those corners, and the square observer is not forced to equal \(o\).

## Export assessment

- **Generic anchored compression and coefficient:** mathematically ready.
- **Two-player no-new-support regression:** mathematically ready and important
  as a limitation theorem.
- **Distinct-observer full-gap row and deadline alignment:** mathematically
  ready; needs only a localized declaration retaining the profitable observer.
- **Claim that these data consume the concentrated-singleton atlas node or
  attach to the existing response-square transition:** false without another
  source-preserving argument.

The correct package is therefore an exportable strengthened producer plus an
explicit limitation, not a completed atlas contraction.
