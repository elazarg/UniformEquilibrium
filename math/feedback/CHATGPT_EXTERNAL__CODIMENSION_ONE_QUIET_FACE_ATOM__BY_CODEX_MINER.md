# Independent review of the codimension-one quiet-face atom

Reviewer: `CODEX_MINER`

Verdict: **REVISE -> PASS for (5)--(8) and the finite-row conclusion after
one mandatory compactness repair.**  The reach conditioning and all displayed
atom constants are correct.  The limit continuation is a limit of actual
suffix continuations (and can be kept in the closed terminal-semantic
carrier); it need not itself be the payoff of an actual behavioral profile.
Thus “actual restricted continuation vector” must be replaced by
“terminal-semantic carrier-limit continuation vector” or simply “the limiting
continuation vector.”  The novelty audit also needs the precise prior
comparisons listed below.

## 1. Setup and witness localization

Fix five players, an omitted player `w`, and four survivors `J`.  From
`eta(r^{-w})=0`, choose restricted profiles `sigma_n` whose maximum survivor
debt is `epsilon_n -> 0`, and quietly lift them to `q_n`.  Exact deletion
naturality preserves every survivor payoff, arbitrary behavioral-deviation
payoff, and cap.  Hence every survivor debt at `q_n` is at most `epsilon_n`.

Since `eta(r)=a>0`, every ambient profile has maximum debt at least `a`.
For large `n`, `epsilon_n<gamma<a`, so the only coordinate that can carry the
ambient lower bound is `w`.  The quiet lift prescribes `w` to literal Never.
Although its cap need not be attained, for every `gamma<a` exact stopping-law
disintegration/pure-time extremality supplies a finite deterministic time
`t_n` with gain at least `gamma`.  No stationary-deviation restriction is
used.

This is the one-player specialization of the reviewed operational
essential-support reduction.  The note is correct not to claim the deletion
inequality itself as new.

## 2. Reach and suffix conditioning

Let `rho_n` be joint survivor survival strictly before `t_n`; because `w` is
Never, this is also `w`'s opponent-survival factor.  Let `theta_n` be the
restricted suffix beginning at that live date.  Exact common-prefix
factorization gives

```text
gamma <= rho_n * Delta_n.
```

All terminal and nonabsorption values lie in `[-M,M]`, so
`Delta_n<=2M`.  Consequently the inequality itself first proves `M>0`, then

```text
rho_n >= gamma/(2M),
Delta_n >= gamma
```

because `rho_n<=1`.  It would improve the statement to record `M>0` before
displaying divisions by `M`.

For a survivor `i`, take an arbitrary behavioral deviation in `theta_n` and
splice it after the unique all-Continue history of length `t_n`, matching the
prescribed strategy before that history.  The prefix absorption terms cancel,
and the suffix payoff improvement is multiplied by exactly `rho_n`.  The
root restricted debt bound therefore gives

```text
rho_n * debt_i(theta_n) <= epsilon_n.
```

Taking the maximum over the four survivors proves

```text
Expl(theta_n) <= epsilon_n/rho_n
              <= (2M/gamma) epsilon_n -> 0.
```

This argument is valid for unrestricted behavioral suffix deviations.  The
most precise existing source correspondence is the common-prefix payoff
factorization underlying
`quittingRelativePureTimeTerminalValue_sub_prefixTransport` and
`quittingPureTimeSuffixRegret_le` in
`UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`,
together with the deletion naturality declarations already cited.

## 3. Coalition pigeonhole and constants

At the first row of `theta_n`, write the product probability of survivor
coalition `A` as `p_n(A)`.  For nonempty `A`,

```text
g_n(A)=r_w(A union {w})-r_w(A),
```

while for `A=empty`, `g_n(empty)` is the singleton payoff minus `w`'s payoff
from the next all-Continue suffix.  Hence `|g_n(A)|<=2M` and

```text
gamma <= Delta_n = sum_A p_n(A) g_n(A)
                    <= sum_A p_n(A) [g_n(A)]_+.
```

There are exactly `2^4=16` subsets of the survivor set.  For each `n`, some
`A_n` therefore satisfies

```text
p_n(A_n) [g_n(A_n)]_+ >= gamma/16.
```

A finite-label subsequence fixes one coalition `A`.  Since
`[g_n(A)]_+<=2M` and `p_n(A)<=1`, respectively,

```text
p_n(A) >= gamma/(32M),
g_n(A) >= gamma/16.
```

Multiplication by the independent reach floor gives exactly

```text
rho_n p_n(A) >= gamma^2/(64M^2).
```

There is no missing factor of sixteen or two.  A strict subsequence preserves
both `epsilon_n -> 0` and all eventual inequalities.

The event interpretation is also correct and should remain explicit.  If
`A` is nonempty, `rho_n p_n(A)` is an actual first-absorption atom of the
quiet profile, and the outsider deviation changes its terminal coalition to
`A union {w}`.  If `A` is empty, the quiet profile does **not** absorb on that
row; only the counterfactual pure-time deviation has the singleton terminal
atom `{w}`.  Thus the theorem always gives an absolute counterfactual atom,
but gives an actual quiet-source terminal atom only in the nonempty arm.

## 4. Compactness repair

For every survivor, the two one-row endpoint deviations at the first row of
`theta_n` are legal behavioral deviations.  Their local regrets are bounded
by `Expl(theta_n) -> 0`.  Extract subsequences of:

- the finite product roots;
- the next-suffix payoff vectors for the four restricted coordinates;
- the omitted player's next-suffix payoff coordinate (needed when
  `A=empty`); and
- if desired, `rho_n` itself.

The root expected-payoff and endpoint formulas are continuous in this finite
data.  The limiting root is therefore exact one-stage Nash for the four
survivors at the limiting continuation vector, and the fixed-coalition mass
and outsider-toggle lower bounds persist.

What compactness alone does **not** prove is that this limiting continuation
vector is the payoff of an actual restricted behavioral profile.  Actual
terminal payoff is not closed under escaping clocks: finite stopping times
can diverge while their strategies converge pointwise to Never.  The safe
strong statement is that, after carrying the full payoff/cap suffix pairs,
their limit lies in the closed restricted terminal-semantic carrier.  That is
enough for the exact one-stage Nash conclusion.  The phrase “at its actual
restricted continuation vector” is therefore an overclaim and is the sole
mathematical wording repair required for (5)--(8)'s compact output.

Similarly, the limiting scalar `rho` need not come with a single actual
prefix that reaches the limiting row.  The theorem's strongest actual
provenance remains the uniform family of finite rows before passage to the
limit.

## 5. Duplicate and novelty audit

The following nearby results must be distinguished.

1. `QuittingPaidFirstDisagreementRow.gain_le_liveMass` in
   `TerminalSemanticPaidFirstDisagreement.lean` already packages the
   division-free implication “positive edge gain forces a quantitative live
   mass.”  Thus the reach half of (5) is existing checked structure, although
   the present use of the exact terminal maximum `M` may be numerically
   tighter than the canonical reward bound.

2. Theorem 3.1 of
   `notes/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`
   already proves a quantitative reached nonempty atom from a codimension-one
   quiet lift, under the extra strict solo-deficit margin.  Its player count,
   constants, and conclusion differ: it has three survivors and forces an
   actual nonempty atom.  The present five-player result removes the solo
   margin but consequently permits the empty/counterfactual singleton arm.

3. `notes/CODEX_EULER__FIN5_QUIET_WHOLE_LAW_ATOM_PAID_CONNECTOR.md`
   retains a separately supplied survivor atom under complete-law
   interpolation and co-realizes an omitted-player paid row.  It does not
   derive the present `gamma^2/(64M^2)` atom from the quiet restricted
   approximation itself.

4. The reviewed sharp deletion passport proves only a positively reached row
   with an unweighted full-gap toggle and explicitly disclaims a quantitative
   row-mass floor.  Equations (7)--(8) are a genuine strengthening of that
   interface.

No checked declaration located in the named deletion/path subtrees packages
the combination of suffix exploitability (6), a fixed coalition label, and
the absolute atom floor (8).

## 6. Remaining sections and scope

The macroscopic-repair bounds (9)--(11) are correct.  Coupling the new law to
Never mismatches only if `w` ever Quits, with probability at most `alpha` in
the presence of survivor absorption.  Prescribed values and each fixed
survivor deviation value move by at most `2M alpha`; taking cap suprema and
then debt costs `4M alpha`.  The best-response cap of `w` is unchanged when
only `w`'s prescribed strategy is replaced, and its prescribed payoff moves
by at most `2M alpha`, proving (11).

The five-player table boundary is exact: all four survivors quitting gives
the restricted and quiet profiles payoff zero, the omitted player gains one
by joining, and all five quitting is nevertheless a pure exact equilibrium
with payoff one.  Thus labelwise face passports do not combine into a
nonexistence result.

For the initial deletion inequality outside the five-player application,
either assume the survivor set `J` is nonempty or define the inner extrema by
an inserted-zero convention.  As written, the inner min/max are undefined
for a singleton ambient player.  This does not affect the new Fin5 theorem.

After the compactness and source-audit repairs, (5)--(8) are valid new
ordinary mathematics.  They remain internal rather than export-ready because
they supply no alignment between the atom and an existing Bellman/floor/rank
consumer, and the empty arm need not produce an atom of the actual quiet
profile.
