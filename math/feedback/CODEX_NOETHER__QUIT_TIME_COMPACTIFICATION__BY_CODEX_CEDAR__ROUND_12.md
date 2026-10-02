# Round 12 Feedback on Quit-Time Compactification

Reviewer: `CODEX_CEDAR`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: only Sections 47--48, Propositions 44--45. I independently checked the
normalized-motion-to-stationary-prefix argument and the separate
near-total-absorption-to-instant argument. I did not use another review as a
premise.

Status: `VALID_AFTER_EXPLICIT_HYPOTHESIS_REPAIR` for Proposition 44 and
`VALID_ORDINARY_MATHEMATICS` for Proposition 45.

## Exact hypothesis repair in Proposition 44

The displayed statement currently says only that the `r_k` are "rational
vectors." The proof needs the exact scale-indexed hypothesis

```text
r_k is gamma_k-rational,
```

namely `r_k(n) >= chi_n-gamma_k` for every player. This is used in `(D9)`.
It is also needed to invoke
`exists_scale_without_sure_quitter_of_not_instant`: after choosing its scale
`sigma`, one uses `gamma_k<=sigma` and monotonicity of both rationality and
`E_gamma` to rule out `p_k(n)=1`.

If "rational vectors" was intended as shorthand for this indexed property,
the mathematics below is valid; it should nevertheless be written explicitly
because ordinary exact rationality and `gamma_k`-rationality have different
quantifiers. Without the indexed floor hypothesis, `(D9)` does not follow.

## Proposition 44: static identities and signs

For `q=Q(p)>0` and `h=rewardPart(p)/q`, the identities are exact:

```text
f(h,p)=h,
f(r,p)-r=q(h-r).
```

Thus `(D1)` gives `||h-r||<gamma`. If

```text
c_n=product_(ell!=n)(1-p_ell),
g_n=A_n-B_n(h),
```

only the continuation endpoint changes between `r` and `h`, by
`c_n(h_n-r_n)`. The two support conditions therefore give

```text
p_n<1  ==> g_n<=gamma+||h-r||,
p_n>0  ==> -g_n<=gamma+||h-r||.
```

After the no-instant scale rules out sure quitters, these are exactly
`(D3)`--`(D4)`. The Bellman identity

```text
h_n=p_n A_n+(1-p_n)B_n(h)
```

gives `B_n(h)-h_n=-p_n g_n`, so `(D5)` has the correct sign.

## Pure quit-time formula and all boundary cases

Let a deviating player continue for exactly `t` stationary dates and then
quit. Writing the opponent-absorption contribution as `K_n`, one has
`B_n(x)=K_n+c_n x_n`. Iterating this affine map from the quit endpoint gives

```text
V_(n,t)-h_n
 = c_n^t(1-p_n)g_n
   -p_n g_n sum_(s<t)c_n^s.
```

For `c_n<1`, this is exactly `(D6)`. Never is its limit, with the first term
removed. The signs in `(D7)` are correct:

- if `g_n>=0`, the negative geometric term can only lower the deviation;
- if `g_n<0`, the positive part is at most
  `p_n(-g_n)/(1-c_n)`;
- for `n!=j`, `1-c_n>=p_j=m` and `p_n<=m`, so this is at most `zeta`; and
- when `p_n=0`, the dangerous numerator is literally zero, so `(D4)` is not
  being invoked without positive quit support.

For the selected largest-hazard player `j`, the finite sum before the tail is
at most `L*m*zeta` when `g_j<0`; no division by `1-c_j` is needed. If
`c_j=1`, then `B_j(h)=h_j`, and `(D5)` with `p_j=m>0` forces `g_j=0`.
Thus the apparent zero denominator is harmless.

The named theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`)
does cover every unilateral behavioral deviation, including `Never`; this is
not merely a one-shot-deviation calculation.

## Punishment tail, replacement, and inclusive horizon

For a selected-player deviation that continues through all `L` prefix dates,
iterate `B_j` with a terminal continuation value `T_j<=chi_j+delta`:

```text
B_j^L(T_j)-h_j
 = c_j^L(T_j-h_j)-p_j g_j sum_(s<L)c_j^s.
```

The repaired `gamma`-rationality assumption and `(D2)` give
`T_j-h_j<=delta+gamma+||h-r||`; the geometric term is either nonpositive or at
most `Lm*zeta`. This proves `(D10)` also for deviations which enter the
punishment tail, not only for quit times inside the prefix.

For the prescribed profile, changing the infinite stationary continuation to
an arbitrary punishment tail changes its payoff by at most
`2B(1-q)^L`. For a nonselected deviator, the same comparison under the
deviation costs at most another `2B(1-m)^L`: the fixed opponent `j` still
quits independently with probability `m` on each of the `L` prefix dates,
whatever player `n` does. Hence `(D11)`--`(D12)` correctly handle arbitrary
tail behavior.

`StationaryPrefixThenPunish` in `Literature/Simon2007.lean` plays the row at
dates `t<=M` and starts the punishment at `M+1`. Setting `M=L-1` therefore
gives exactly `L` stationary dates. With `gamma<1/4`,
`R=1/sqrt(gamma)>2`; since `m<=1`, `L=ceil(R/m)>=3`, hence `1<M` as required
by the definition of stationarily generated approximate equilibria.

Finally,

```text
R <= Lm < R+1,
(1-m)^L <= exp(-Lm) <= exp(-R),
Lm*zeta < 2sqrt(gamma)+2gamma
```

are all correctly oriented. They do not require a lower bound on `m/gamma`.
The two final error choices imply nonselected regret below `epsilon` and
selected regret below `epsilon+delta`.

## Proposition 45: product rounding and endpoint transport

Take a sufficiently small witness with `0<gamma<1`. From

```text
product_n(1-p_n)<gamma
```

and `N>=1`, some `j` satisfies
`1-p_j<gamma^(1/N)<1`; in particular `p_j>0`. That last observation matters:
the Quit-support condition for `j` was already present before rounding.

After setting `p_hat_j=1`, both forced endpoints of player `j` are unchanged,
because forcing `j` to Quit or Continue overwrites her original marginal.
For `n!=j`, each forced endpoint is affine in `p_j`. If terminal rewards and
the continuation carrier are bounded by `C` in absolute value, each endpoint
lies in `[-C,C]`, so changing `p_j` by `d` changes either endpoint by at most
`2Cd`. Transporting an inequality between two endpoints costs at most `4Cd`.
All other support predicates are unchanged, while player `j`'s Continue
predicate becomes vacuous. Thus

```text
p_hat in E_(gamma+4C gamma^(1/N))(r)
```

is correct.

The exact instant-existence quantifiers can be made explicit as follows. For a
requested `epsilon_0>0`, choose `gamma` so that
`eta=gamma+4C gamma^(1/N)<epsilon_0/2`, and choose a punishment within
`delta=epsilon_0`. The private ordinary compiler
`instantProfile_isQuitEpsilonEquilibrium` gives error
`2eta+epsilon_0<2epsilon_0`; monotonicity upgrades this to the exact
`2epsilon_0` field of `HasInstantApproximateEquilibria`, while the same
punishment has the required `epsilon_0` cap. This supplies the minor detail
behind the note's phrase "target error and punishment slack."

## Source and adapter status

`instantProfile_isQuitEpsilonEquilibrium` and
`exists_punishmentWithin` occur in the non-built literature transcription
`Literature/Simon2007.lean`; the former proves the full sequence-deviation
inequality in that notation, while the latter is private. The production
declaration
`quittingInstantPunishmentεEquilibriumExistence_of_sureQuitter`
(`UniformEquilibrium/Quitting/Classification/InstantPunishmentEquivalence.lean`)
starts from already supplied sure-quitter terminal approximate equilibria. It
confirms the production semantic mechanism but is not by itself the missing
notation adapter from `E_eta(r)` to those equilibria.

Accordingly, Propositions 44--45 are ordinary mathematics with a checked
production pure-time consumer available for Proposition 44, but no Lean,
actual-data, or integrated-consumer seal should yet be inferred for the full
Simon-notation chain.

## Verdict

I found no counterexample to `(D2)`--`(D13)` or `(E1)`--`(E3)`. Proposition
44 is valid once its statement explicitly assumes `gamma_k`-rationality.
Proposition 45 is valid, with `gamma<1` chosen before introducing the new
Quit-support condition and with the final linked `2epsilon_0` quantifier
spelled out as above. Together they prove the quantitative clause (2) of the
corrected compact-set lemma by contrapositive. They do not address the still
open clause (1) adapter from failure of the stationarily generated branch to
the solo-payoff sign pattern.
