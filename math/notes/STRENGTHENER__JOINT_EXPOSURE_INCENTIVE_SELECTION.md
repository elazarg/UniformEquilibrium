# Joint singleton-exposure and deadline-incentive selection

Author: `STRENGTHENER`

## Status

Ordinary mathematics, not checked in Lean. The sharp selection theorem below
is independently derived from the stopping-law mixture identity. It recovers
the optimal coefficient in incentive-aware clock compression and gives an
exact two-player equality example.  The positive-anchor application is valid
provided `Y_t` is the gain of the **whole copied-prefix completion**, not the
raw pure-deadline payoff gain.  This formulation automatically retains the
pre-anchor term which was missed in the first clock-compression draft.  The
nonvacuous atlas consequence is conditional on the selected singleton owner
being inactive at the minimum: then cofinal compressed endpoints preserve
vanishing owner debt and co-realize a fixed nonowner paid row.  The equality
example shows that no active-owner support descent follows from the two
moments alone.

## 1. Abstract sharp theorem

Let `(T,pi)` be a finite or countable probability space. Let `Y` be
integrable and let

\[
 0\le s_t\le p,\qquad Y_t\le d,
\]

where `0<p<=1` and `d>=0`, and suppose

\[
 \mathbb E_\pi[s]=\mu,
 \qquad
 \mathbb E_\pi[Y]=0.
 \tag{1}
\]

Fix `lambda` with

\[
 0\le\lambda<\mu\le p.
\]

Then there exists `t` in the positive `pi`-support such that

\[
 s_t>\lambda
 \tag{2}
\]

and

\[
 \boxed{
 Y_t\ge -\frac{p-\mu}{\mu-\lambda},d.}
 \tag{3}
\]

Consequently, if `d-Y_t` is the debt of the selected pure completion, then

\[
 \boxed{
 d-Y_t\le\frac{p-\lambda}{\mu-\lambda},d.}
 \tag{4}
\]

For the unanchored stopping law, `p=1`, giving constants

\[
 \frac{1-\mu}{\mu-\lambda}
 \quad\text{and}\quad
 \frac{1-\lambda}{\mu-\lambda}.
\]

### Proof

Put `H={t:s_t>lambda}` and `w=pi(H)`. Since `s<=p` on `H` and
`s<=lambda` off `H`,

\[
 \mu\le pw+\lambda(1-w),
\]

so

\[
 w\ge\frac{\mu-\lambda}{p-\lambda}>0,
 \qquad
 1-w\le\frac{p-\mu}{p-\lambda}.
 \tag{5}
\]

Using `E[Y]=0` and `Y<=d`,

\[
 \mathbb E[Y\mathbf1_H]
 =-\mathbb E[Y\mathbf1_{H^c}]
 \ge-d(1-w).
\]

Hence some `t in H` has

\[
 Y_t\ge-d\frac{1-w}{w}
 \ge-d\frac{p-\mu}{\mu-\lambda},
\]

which proves (2)--(3). Adding `d` gives (4).

The proof needs no lower bound on `Y_t`. This matters because a pure deadline
can be arbitrarily worse than prescribed play even though every pure deadline
gain is bounded above by the source debt.

## 2. Stopping-law interpretation, including a positive anchor

First take anchor zero.  Fix the opponents of owner `j`. Let `pi_t` be the
probability of deterministic deadline `t` in `j`'s complete stopping-law
mixture, including Never. Let `V_t` be `j`'s payoff from that deadline, let
`U` be prescribed payoff, let `B` be the unrestricted behavioral cap, and put

\[
 Y_t=V_t-U,
 \qquad d=B-U.
\]

Pure-time extremality and affinity in `j`'s stopping law give

\[
 \sum_t\pi_tY_t=0,
 \qquad Y_t\le d.
 \tag{6}
\]

Let `s_t` be the opponent-survival probability exposed by replacing `j` with
deadline `t`, and put `s_infinity=0`. Then the prescribed singleton law mass is

\[
 \mu=\sum_t\pi_ts_t.
 \tag{7}
\]

For this unanchored application, `p=1`.  The selected completion has
singleton stage mass `s_t>lambda`. Since changing only `j`'s strategy leaves
`B_j` unchanged, its debt is exactly

\[
 B-V_t=d-Y_t,
\]

and (4) follows.

Now fix a positive anchor `a` and suppose the post-anchor singleton mass
`m` is positive; then the owner's own anchor-survival probability `p_a` is
positive.  Conditional on the owner reaching `a`, write
`alpha_t` for its complete conditional stopping-time law on
`{a,a+1,...,infinity}`.  For every such `t`, let `tau_t`:

- copy the owner's source strategy before `a`;
- use the deterministic conditional deadline `t` after `a`; and
- keep every opponent literally unchanged.

Put

\[
 Y_t=U_j(\tau_t)-U_j(\sigma).
\]

The source strategy is the `alpha`-mixture of these **whole completions**, so

\[
 \mathbb E_\alpha[Y]=0.
 \tag{8}
\]

Changing only `j` leaves its cap fixed.  Hence the selected target debt is
again `d-Y_t`, and nonnegativity of that debt gives `Y_t<=d`.  If `beta_t` is
the singleton stage mass exposed by `tau_t` (and `beta_infinity=0`), then

\[
 0\le\beta_t\le p_a,
 \qquad
 \mathbb E_\alpha[\beta]=m,
\]

where `p_a` is the copied probability that the owner reaches the anchor and
`m` is the source singleton mass after the anchor.  Applying the abstract
theorem with `p=p_a`, `s=beta`, and `mu=m` gives

\[
 d_j(\tau_t)\le \frac{p_a-\lambda}{m-\lambda}d_j(\sigma).
 \tag{9}
\]

This is equivalent to the corrected nonnegative-regret proof with its explicit
pre-anchor term `e`.  What is invalid is to use the raw pure-deadline gain
`V_t-U` at positive anchor; what is valid is the zero-mean gain of the whole
copied-prefix completion.

This is the sharp joint version of clock compression: it selects mass and
incentive on the same actual deadline, rather than first selecting a large
exposure and then hoping its payoff is acceptable.

## 3. Exact sharp two-player regression

Take parameters

\[
 0\le\lambda<\mu<1,
 \qquad d>0,
 \qquad
 w=\frac{\mu-\lambda}{1-\lambda}.
\]

There are two players, owner `j` and opponent `k`. Player `k` Continues surely
at date zero and at date one Quits with probability `1-lambda`, otherwise
Never. Player `j` chooses deadline zero with probability `w` and deadline one
with probability `1-w`.

Set `j`'s rewards to

\[
 r_j(\{j\})=r_j(\{k\})=0,
 \qquad
 r_j(\{j,k\})=\frac{d}{w(1-\lambda)},
 \tag{10}
\]

and give `k` zero on every coalition. The two relevant pure-deadline payoffs
and exposures are

\[
 (s_0,V_0)=(1,0),
 \qquad
 (s_1,V_1)=\left(\lambda,\frac d w\right).
\]

The prescribed singleton mass is

\[
 w+(1-w)\lambda=\mu.
\]

All later deadlines and Never pay zero, so `B_j=V_1`. Prescribed payoff is
`U_j=(1-w)V_1`, and source debt is exactly `d`. Therefore

\[
 Y_1=d,
 \qquad
 Y_0=-\frac{1-w}{w}d
 =-\frac{1-\mu}{\mu-\lambda}d.
 \tag{11}
\]

The only deadline with exposure strictly above `lambda` is date zero, and it
attains equality in (3). Thus the constant is sharp even for an actual
two-player quitting game with two finite deadlines.

This game has the all-Never zero-debt equilibrium. It is not a positive-gap
counterexample; it is an exact regression against inferring active-owner debt
contraction from the two moment identities.  The identities say nothing about
new debt on other coordinates; the separate equal-date matching example in
`CODEX_ROOT__INCENTIVE_AWARE_SINGLETON_CLOCK_COMPRESSION.md` shows that even a
zero-debt owner compression can open order-one debt on an opponent.

## 4. The complementary exposure--payoff polarity

The same two moments give a second sharp formulation.  Fix `kappa>0` and
assume `p>mu`.  Then either

\[
 \exists t,\qquad s_t>\lambda
 \quad\hbox{and}\quad Y_t>-\kappa,
 \tag{12}
\]

or there are a high-exposure deadline `h` and a low-exposure deadline `l`
such that

\[
 s_h>\lambda,\qquad s_l\le\lambda,
\]

\[
 Y_h\le-\kappa,
 \qquad
 Y_l\ge \kappa\frac{\mu-\lambda}{p-\mu},
 \tag{13}
\]

and hence

\[
 U_j(\tau_l)-U_j(\tau_h)=Y_l-Y_h
 \ge \kappa\frac{p-\lambda}{p-\mu}.
 \tag{14}
\]

Indeed, if (12) fails, every member of `H={s>lambda}` has
`Y<=-kappa`.  With `w=pi(H)`,

\[
 \mathbb E[Y1_{H^c}]=-\mathbb E[Y1_H]\ge\kappa w.
\]

The failure of (11) and `E[Y]=0` force `w<1`.  Some low-exposure deadline
therefore has gain at least `kappa w/(1-w)`.  Equation (5) and monotonicity of
`w/(1-w)` give (13), and comparison with any supported high-exposure deadline
gives (14).  If `p=mu`, equality `E[s]=p` forces `s=p` almost surely; then
some high-exposure deadline has nonnegative `Y`, so the first arm holds for
every positive `kappa`.

Thus failure of a good high-exposure completion cannot be silent: it creates a
source-matched paid pair of pure deadlines with the favorable deadline on the
low-exposure side.  The two-player regression above attains equality in
(13)--(14), so these constants are sharp too.  This is paid orientation data,
not yet a cap-curvature square or an executable return.

There is a stronger provenance form.  Condition the owner's post-anchor
stopping law on `H` and `H^c`, and call the resulting actual whole-law profiles
`sigma_H` and `sigma_L`.  They copy the same source prefix and every opponent,
and the original source is literally their whole-stopping-law mixture:

\[
 \sigma=w\sigma_H+(1-w)\sigma_L
 \quad\text{in the owner's complete stopping law}. \tag{15}
\]

The high endpoint has post-anchor singleton mass `>lambda`; the low endpoint
has mass `<=lambda`; and in the second polarity arm

\[
 U_j(\sigma_H)-U_j(\sigma)\le-\kappa,
 \qquad
 U_j(\sigma_L)-U_j(\sigma)\ge\kappa\frac{w}{1-w},
\]

so

\[
 U_j(\sigma_L)-U_j(\sigma_H)
 \ge\frac{\kappa}{1-w}
 \ge\kappa\frac{p-\lambda}{p-\mu}. \tag{16}
\]

This produces a literal same-opponents stopping-law chord through the source,
not just two detached dates.  The owner's cap is identical at all three
profiles.  Other players' caps remain only convex along the chord, so (15)
does not yet give a signed total-debt curvature.

## 5. Cofinal minimum-source consequence for an inactive owner

Let a selected minimum joint law have singleton atom `{j}` of mass `mu>0`,
and let its retained causal chronology be fixed. Suppose

\[
 d_j(z_*)=0.
 \tag{17}
\]

Exact cap-stack debt scaling, convergence of the suffix semantic pairs to
`z_*`, and convergence of the stack Continue products to one imply that the
owner debt of the literal prefixed reference profiles tends to zero. The
post-anchor singleton mass converges to `mu`.

Fix any `0<lambda<mu`. Apply the **corrected copied-prefix anchored theorem**
at every sufficiently deep reference profile. The denominators
`mu_n-lambda` stay uniformly positive, while `p_n<=1`; hence the selected
literal owner completions satisfy

\[
 \Pr(\{j\}\text{ at the selected deadline})>\lambda,
 \qquad
 d_j(\tau_n)\longrightarrow0.
 \tag{18}
\]

All opponents are unchanged, the conditional deadline is selected from the
same source stopping law, and all targets use cofinally deep ranks of the one
retained chronology.  The source root word before the anchor is copied
literally.  Its cap--Nash certificate remains a theorem about the **unmodified
suffix only**; no target-side cap--Nash claim is made.

Under a terminal exploitability witness of gap `gamma`, for large `n` player
`j` cannot be the gap coordinate at `tau_n`.  The checked theorem
`HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` therefore
selects some `o_n!=j` and a paid row of the full terminal gap on that exact
profile.  Finiteness of `Fin 4` fixes `o_n=o` on a subsequence.  Its two pure
plans must first disagree no later than the selected deadline: if their first
disagreement date were later, they would use identical actions through the
mark, and on every still-live history `j` Quits surely at the mark.  They would
therefore induce identical terminal outcomes pathwise, contradicting the
row's positive paid gain.  Therefore the endpoints
co-realize

- fixed singleton stage mass `>lambda`;
- vanishing unrestricted owner debt;
- one fixed nonowner full-gap paid row beginning no later than the mark; and
- by `gain_le_liveMass`, the division-free pre-mark reach bound
  `gamma <= 2 * quittingRewardBound reward * liveMass`; and
- the literal source chronology and opponent strategies.

This is genuinely source-dependent and does not follow from the universal
constant concentrated-packet construction.

It still does not control the other three debts, make the copied cap stack
exact for the changed target, or produce a Bellman return. Hence it is a
stronger actual endpoint interface, not a complete consumer.

## 6. Unconditional asymptotic dispatch on the retained minimum chronology

The inactive-owner premise is unnecessary for a weaker but still
source-attached dichotomy.  Let `sigma_n` be the literal prefixed reference
profiles from the retained minimum chronology.  Thus

\[
 D(\sigma_n)\longrightarrow D_*,
\]

and suppose the post-anchor singleton mass tends to `mu>0`.  Fix
`0<lambda<mu`.  After passing to a subsequence, exactly one of the following
two useful alternatives is available.

### Almost-safe concentrated completion

There are source-supported anchored completions `tau_n` with

\[
 \Pr_{\tau_n}(\{j\}\text{ at its selected date})>\lambda,
 \qquad
 d_j(\tau_n)\le d_j(\sigma_n)+o(1).
 \tag{19}
\]

### Fixed-gain owner transfer

There is a constant `g>0` and anchored low-exposure completions `rho_n` such
that

\[
 U_j(\rho_n)-U_j(\sigma_n)\ge g,
 \qquad
 d_j(\rho_n)\le d_j(\sigma_n)-g,
 \tag{20}
\]

and global minimum provenance forces

\[
 \sum_{i\ne j}\bigl(d_i(\rho_n)-d_i(\sigma_n)\bigr)
 \ge g-o(1).
 \tag{21}
\]

The second arm also retains, at the same source and anchor, a high-exposure
completion `tau_n` with singleton mass `>lambda` which is worse for `j` by a
fixed amount.  Thus it is a fixed source-matched paid transfer with the exact
exposure-reversing orientation (13)--(14), not merely the abstract existence
of a profitable deviation.

To prove the dichotomy, let `a_n` be the supremum of the completion gains over
the source-supported set `{beta>lambda}`.  This set has positive conditional
mass.  If `limsup a_n>=0`, select an `o(1)`-maximizer and obtain (19).
Otherwise, on a subsequence there is `kappa>0` such that every supported
high-exposure completion has gain at most `-kappa`.  Apply (12)--(14).  Since
`m_n->mu`, `p_n<=1`, and eventually `m_n>(mu+lambda)/2`, the favorable
low-exposure completion has gain at least, for example,

\[
 g:=\frac{\kappa(\mu-\lambda)}2>0.
\]

Own-strategy replacement leaves `j`'s cap unchanged, proving the second part
of (20).  Finally

\[
 D(\rho_n)-D(\sigma_n)
 =-\bigl(U_j(\rho_n)-U_j(\sigma_n)\bigr)
  +\sum_{i\ne j}(d_i(\rho_n)-d_i(\sigma_n)),
\]

while `D(rho_n)>=D_*` and `D(sigma_n)=D_*+o(1)`, which proves (21).

This is the strongest conclusion furnished by the two moments plus minimum
provenance.  It is not the universal concentrated-packet adapter: its second
arm records an exact, fixed-gain debt transfer from the actual near-minimum
source, while its first arm compares the selected owner's debt to that same
source.  Neither arm controls total target debt from above.

## 7. Active-owner verdict

If `d_j(z_*)>0`, (4) gives only a finite multiplicative upper bound on the
compressed owner debt. Its coefficient is at least one because `p>=mu`.
The sharp regression shows that every high-exposure deadline may increase
the owner debt by exactly this factor while all positive payoff gain is
confined to low-exposure deadlines.

Whole-stopping-law debt convexity does not reverse this conclusion. Mixing a
sharp high-exposure completion back toward the source gives an affine owner
debt lying above the source value; it does not produce a drain. Other
coordinates may acquire order-one debt as well.

Therefore the proposed moments do not yield minimum-fiber support descent for
an active owner.  They do yield the exact exposure--payoff polarity
(12)--(14) and the minimum-source transfer account (20)--(21).  Turning that
transfer into total debt descent or a renewable cap-curvature square still
requires a cross-coordinate restriction, a leakage estimate, or a separate
source-matched response square.

## 8. Lean handoff

The abstract theorem should first be formalized independently of quitting
games as a finite/countable weighted selection lemma. The quitting adapter
then uses:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` for the
  complete stopping-law expectation;
- the stopping-law reconstruction API for conditional high/low laws;
- pure-time extremality of unrestricted terminal caps;
- `quittingContinuationBestResponseValue_update_self` for invariance of a
  player's cap under its own strategy replacement;
- `FinFourMinimumAtomChronology.prefixedTailMass_eq_continueProduct_mul_terminalMass`;
- `FinFourMinimumAtomChronology.tendsto_prefixedTailMass`; and
- `quittingTerminalDeviationDebt_capNashRootStack_eq` for exact coordinatewise
  cap-stack debt scaling.

The paid co-realization additionally uses
`HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at`.  Its
`QuittingPaidFirstDisagreementRow.gain_le_liveMass` field gives the usual
positive reached-mass floor; the inequality `start<=selectedDeadline` is the
new elementary pathwise adapter explained in Section 5.

The relevant checked files inspected were
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`,
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`,
`UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean`,
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`,
`Research/Quitting/AnchoredSingletonClockCompression.lean`, and
`Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`.
The last two currently expose probability-law compression and chronology, not
the incentive-weighted selection proved here.

The two-player regression should be kept as a boundary theorem or exact test,
because it certifies sharpness and blocks an invalid active-owner descent
adapter.
